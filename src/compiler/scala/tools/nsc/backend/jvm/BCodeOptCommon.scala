/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.{ProdConsAnalyzer, UnBoxAnalyzer, Util}
import asm.tree.analysis.SourceValue
import asm.tree._

import scala.collection.{ mutable, immutable }
import scala.Some
import collection.convert.Wrappers.JListWrapper
import collection.convert.Wrappers.JSetWrapper

/**
 *  Utilities shared across intra-method and inter-procedural optimizations.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOptCommon extends BCodeTypes {

  import global._

  // volatile so that Worker2 threads see it
  @volatile var isInliningDone          = false // affects only which checks (regarding dclosure usages) are applicable.
  @volatile var isClassNodeBuildingDone = false // allows checking whether Worker1 thread is done, e.g. to register a new method descriptor as BType.

  final def assertPipeline1Done(msg: String) {
    assert(isClassNodeBuildingDone, msg)
  }

  val elidedClasses: java.util.Set[BType] = java.util.Collections.newSetFromMap(
    new java.util.concurrent.ConcurrentHashMap[BType, java.lang.Boolean]
  )

  def createBCodeCleanser(cnode: asm.tree.ClassNode, isInterClosureOptimizOn: Boolean): BCodeCleanserIface  // implemented by BCodeOptIntra
  def createQuickCleanser(cnode: asm.tree.ClassNode): QuickCleanserIface                                    // implemented by BCodeOptIntra

  trait BCodeCleanserIface {
    def intraMethodFixpoints(full: Boolean)
  }

  trait QuickCleanserIface {
    def basicIntraMethodOpt(mnode: asm.tree.MethodNode)
  }

  /**
   *  Single-access point for requests to parse bytecode for inlining purposes.
   *  Given the BType of a class with internal name,
   *  `codeRepo` allows obtaining its bytecode-level representation (ClassNode).
   *  It's possible to find out whether a ClassNode was compiled in this run, or parsed from an external library.
   * */
  object codeRepo {

    val parsed  = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]
    val classes = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]

    def containsKey(bt: BType): Boolean = { (classes.containsKey(bt) || parsed.containsKey(bt)) }

    /**
     *  must-single-thread
     */
    def getFieldOrNull(bt: BType, name: String, desc: String): FieldNode = {
      try { getField(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the FieldInsnNode have compiled?
      }
    }

    /**
     *  must-single-thread
     */
    def getMethodOrNull(bt: BType, name: String, desc: String): MethodNodeAndOwner = {
      try { getMethod(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
    }

    /**
     *  @return None if not found, the MethodNode's access field otherwise.
     *
     *  must-single-thread
     *
     * */
    def getMethodAccess(bt: BType, name: String, desc: String): Option[Int] = {
      val cn = getClassNode(bt) // must-single-thread
      if(cn == null) { return None }
      val iter = cn.methods.iterator()
      while(iter.hasNext) {
        val mn = iter.next()
        if(mn.name == name && mn.desc == desc) {
          return Some(mn.access)
        }
      }
      for(ifaceIName <- JListWrapper(cn.interfaces)) {
        val outcome = getMethodAccess(lookupRefBType(ifaceIName), name, desc)
        if(outcome.nonEmpty) { return outcome }
      }
      if(cn.superName != null) {
        val outcome = getMethodAccess(lookupRefBType(cn.superName), name, desc)
        if(outcome.nonEmpty) { return outcome }
      }
      None
    }

    /**
     * Looks up (parsing from bytecode if needed) the field declared in `bt`
     * given by the combination of field-name and field-descriptor.
     *
     * must-single-thread
     */
    def getField(bt: BType, name: String, desc: String): FieldNode = {
      val cn = getClassNode(bt)
      val iter = cn.fields.iterator()
      while(iter.hasNext) {
        val fn = iter.next()
        if(fn.name == name && fn.desc == desc) {
          return fn
        }
      }

      MissingRequirementError.notFound(s"Could not find FieldNode: ${bt.getInternalName}.$name: ${desc}")
    }

    /**
     * Looks up (parsing from bytecode if needed) the method declared in `bt`
     * given by the combination of method-name and method-descriptor.
     * Keeps looking up over the superclass hierarchy, until reaching j.l.Object
     *
     * @return if found, the MethodNode and the ClassNode declaring it. Otherwise MissingRequirementError is thrown.
     *
     * must-single-thread
     */
    def getMethod(bt: BType, name: String, desc: String): MethodNodeAndOwner = {

      var current = bt

      while(current != null) {
        val cn = getClassNode(current)
        val iter = cn.methods.iterator()
        while(iter.hasNext) {
          val mn = iter.next()
          if(mn.name == name && mn.desc == desc) {
            return MethodNodeAndOwner(mn, cn)
          }
        }
        current = if(cn.superName == null) null else lookupRefBType(cn.superName)
      }

      MissingRequirementError.notFound(s"Could not find MethodNode: ${bt.getInternalName}.${name}${desc}")
    }

    /** must-single-thread */
    def getClassNode(owner: String): asm.tree.ClassNode = { getClassNode(brefType(owner)) }

    /**
     *  Returns the ASM ClassNode for a class that's being compiled or that's going to be parsed from external bytecode.
     *
     *  After this method has run, the following two post-conditions hold:
     *    - `exemplars.containsKey(bt)`
     *    - `codeRepo.containsKey(bt)`
     *
     *  must-single-thread
     */
    def getClassNode(bt: BType): asm.tree.ClassNode = {
      var res = classes.get(bt)
      if(res == null) {
        res = parsed.get(bt)
        if(res == null) {
          res = parseClassAndEnterExemplar(bt)
        }
      }
      assert(exemplars.containsKey(bt))
      res
    }

    /**
     *  can-multi-thread
     * */
    def getClassNodeOrNull(bt: BType): asm.tree.ClassNode = {
      try {
        var res = classes.get(bt)
        if(res == null) {
          res = parsed.get(bt)
          // we can't call parseClassAndEnterExemplar(bt) because in the time window from the checks above and
          // the time parseClassAndEnterExemplar() runs, Worker1 may have added to codeRepo.classes the class we didn't find.
        }
        res
      }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
    }

    /**
     *  Some analyses (e.g., Type-Flow Analysis) and some backend utilities (e,g, `refreshInnerClasses()`)
     *  require `exemplars` to contain entries for all classes the analysis encounters.
     *  A class that is being compiled is already associated to a Tracked instance (GenBCode took care of that).
     *  For a class `bt` mentioned in external bytecode, `parseClassAndEnterExemplar()` adds an entry to `exemplars`.
     *
     *  After this method has run the following two post-conditions hold:
     *    - `exemplars.containsKey(bt)`
     *    - `codeRepo.parsed.containsKey(bt)`
     *
     *  @param bt a "normal" class (see `BType.isNonSpecial`) for which an entry in `exemplars` should be added if not yet there.
     *
     *  @return   the ASM ClassNode after parsing the argument from external bytecode.
     *
     *  must-single-thread
     */
    def parseClassAndEnterExemplar(bt: BType): ClassNode = {
      assert(bt.isNonSpecial,  s"The `exemplars` map is supposed to hold ''normal'' classes only, not ${bt.getInternalName}")
      assert(!containsKey(bt), s"codeRepo already contains ${bt.getInternalName}")

          /** must-single-thread */
          def parseClass(): asm.tree.ClassNode = {
            assert(!containsKey(bt))
            val iname   = bt.getInternalName
            val dotName = iname.replace('/', '.')
            classPath.findSourceFile(dotName) match {
              case Some(classFile) =>
                val cn = new asm.tree.ClassNode()
                val cr = new asm.ClassReader(classFile.toByteArray)
                cr.accept(cn, asm.ClassReader.SKIP_FRAMES)
                parsed.put(bt, cn)
                cn
              case _ => MissingRequirementError.notFound(s"Could not find bytecode for $dotName")
            }
          }

      val cn = parseClass()

      if(exemplars.containsKey(bt)) {
        return cn // TODO check if superName, interfaces, etc agree btw cn and exemplar(bt)
      }

          def enterIfUnseen(iname: String): Tracked = {
            val bt = brefType(iname)
            var exempl = exemplars.get(bt)
            if(exempl == null) {
              parseClassAndEnterExemplar(bt) // recursive call
              exempl = exemplars.get(bt)
            }
            exempl
          }

          def enterIfUnseens(inames: java.util.List[String]): Array[Tracked] = {
            var ifaces: List[Tracked] = Nil
            val iter = inames.iterator()
            while(iter.hasNext) {
              ifaces ::= enterIfUnseen(iter.next())
            }
            if(ifaces.isEmpty) { EMPTY_TRACKED_ARRAY }
            else {
              val arr = new Array[Tracked](ifaces.size)
              ifaces.copyToArray(arr)
              arr
            }
          }

      val tsc       = enterIfUnseen(cn.superName)
      val ifacesArr = enterIfUnseens(cn.interfaces)

      // ClassNode.innerClasses isn't indexed by InnerClassNode.name, this map accomplishes that feat.
      val innerClassNode: Map[String, InnerClassNode] = {
        JListWrapper(cn.innerClasses) map (icn => (icn.name -> icn)) toMap
      }

      val isInnerClass = innerClassNode.contains(cn.name)
      val innersChain: Array[InnerClassEntry] =
        if(!isInnerClass) null
        else {

              def toInnerClassEntry(icn: InnerClassNode): InnerClassEntry = {
                InnerClassEntry(icn.name, icn.outerName, icn.innerName, icn.access)
              }

          var chain: List[InnerClassEntry] = toInnerClassEntry(innerClassNode(cn.name)) :: Nil
          var keepGoing = true
          do {
            // is the enclosing class of the current class itself an inner class?
            val currentOuter = chain.head.outerName
            keepGoing = innerClassNode.contains(currentOuter)
            if(keepGoing) {
              chain ::= toInnerClassEntry(innerClassNode(currentOuter))
            }
          } while(keepGoing)

          chain.toArray
        }

      val tr = Tracked(bt, cn.access, tsc, ifacesArr, innersChain)
      exemplars.put(tr.c, tr) // no counterpart in symExemplars, that's life.

      cn
    }

    /**
     *  This method goes over its argument looking for not-yet-seen TypeNames,
     *  fabricating a Tracked instance for them (if needed by parsing bytecode,
     *  thus the location of this method as utility in codeRepo).
     *
     *  An invariant we want to maintain:
     *    "each internal name mentioned in an instruction that's part of this program
     *     should be associated to a Tracked instance (which implies, associated to a BType instance)"
     *  That invariant guarantees a Type-Flow Analysis can be run anytime,
     *  additionally `refreshInnerClasses()` also relies on `exemplars`.
     *
     *  Without a TypeName for an internal name or method descriptor, the following conversions can't be performed:
     *    from type-descriptor to BType, via `BCodeTypes.descrToBType()`
     *    from internal-name   to BType, via `BCodeTypes.lookupRefBType()`
     *  In turn, BTypes are indispensable as keys to the `exemplars` map.
     *
     *  must-single-thread
     */
    def registerUnseenTypeNames(insns: InsnList) {

        def enterInternalName(iname: String) {
          var bt = brefType(iname)
          if(bt.isArray) {
            bt = bt.getElementType
          }
          if(bt.isNonSpecial && !exemplars.containsKey(bt)) {
            // exemplars can be added *via parsing bytecode* only after all classes being compiled have landed in codeRepo.classes
            codeRepo.parseClassAndEnterExemplar(bt)
          }
        }

        def enterDescr(desc: String) {
          val c: Char = desc(0)
          c match {
            case 'V' | 'Z' | 'C' | 'B' | 'S' | 'I' | 'F' | 'J' | 'D' => ()
            case 'L' =>
              val iname = desc.substring(1, desc.length() - 1)
              enterInternalName(iname)
            case '(' =>
              val mt = BType.getMethodType(desc)
              enterDescr(mt.getReturnType.getDescriptor)
              for(argt <- mt.getArgumentTypes) {
                enterDescr(argt.getDescriptor)
              }
            case '[' =>
              val arrt = BType.getType(desc)
              enterDescr(arrt.getComponentType.getDescriptor)
          }
        }

      val iter = insns.iterator()
      while(iter.hasNext) {
        val insn = iter.next()
        insn match {
          case ti: TypeInsnNode   => enterInternalName(ti.desc) // an intenal name, actually
          case fi: FieldInsnNode  => enterInternalName(fi.owner); enterDescr(fi.desc)
          case mi: MethodInsnNode => enterInternalName(mi.owner); enterDescr(mi.desc)
          case ivd: InvokeDynamicInsnNode => () // TODO
          case ci: LdcInsnNode =>
            ci.cst match {
              case t: asm.Type => enterDescr(t.getDescriptor)
              case _           => ()
            }
          case ma: MultiANewArrayInsnNode => enterDescr(ma.desc)
          case _ => ()
        }
      }

    } // end of method enterExemplarsForUnseenTypeNames()

    def clear() {
      parsed.clear()
      classes.clear()
    }

  } // end of object codeRepo

  //--------------------------------------------------------
  // Tracking of delegating-closures
  //--------------------------------------------------------

  final def isDClosure(iname: String) = closuRepo.isDelegatingClosure(iname)

  final def isMasterClass(bt: BType)  = closuRepo.isMasterClass(bt)

  case class MethodRef(ownerClass: BType, mnode: MethodNode)

  /**
   *  @return the callee, for a MethodNodeInsn, represented as MethodRef. Otherwise null.
   * */
  final def accessedMethodRef(insn: AbstractInsnNode): MethodRef = {
    insn match {
      case mi: MethodInsnNode =>
        val ownerBT = lookupRefBType(mi.owner)
        val mnode   = codeRepo.getMethod(ownerBT, mi.name, mi.desc).mnode
        MethodRef(ownerBT, mnode)
      case _ => null
    }
  }

  /**
   * Terminology for delegating closures
   * -----------------------------------
   *
   * "delegating closure": ("dclosure" for short) an anonymous-closure-class
   *                       created by UnCurry's `closureConversionModern()`.
   *
   * "dclosure endpoint":  method consisting of the closure's body, its name contains "dlgt$".
   *
   * "master class of a dclosure": non-dclosure class declaring one or more dclosure endpoints
   *                               (we say the master class "is responsible for" its dclosures).
   *
   * Invariants for delegating closures
   * ----------------------------------
   *
   * These invariants are checked in `checkDClosureUsages()`
   *
   * The items above exhibit invariants that a "traditional closure" doesn't necessarily guarantee,
   * invariants that can be exploited for optimization:
   *
   *   (a) the endpoint of a dclosure is the single entry point through which
   *       the dclosure may access functionality of its master class.
   *
   *   (b) Initially there's program wide a single callsite targeting any given dclosure-endpoint
   *       (that callsite is enclosed in one of the dclosure's apply() methods).
   *       This may change due to:
   *
   *         (b.1) dead-code elimination, which may remove the instantiation of the dclosure
   *
   *         (b.2) as part of `WholeProgramAnalysis.inlining()`, closure-inlining elides a dclosure-class.
   *               As a result, one or more callsites to the endpoint may occur now in the
   *               "static-HiO" method added to the master class (see `buildStaticHiO`).
   *               Still, all those occurrences can be found by inspecting the master class.
   *               Moreover, a static-HiO method, although public, is itself never inlined
   *               (callsites to it may well be inlined, e.g. in another class).
   *               Thus the following invariant holds:
   *
   *               Callsites to a dclosure endpoint may appear only:
   *                 - either in
   *                     the dclosure (just one callsite), if the dclosure hasn't been inlined;
   *                 - or
   *                     in the master class (one ore more callsites), if the dclosure has been inlined.
   *
   *               (This whole nit-pick about not losing track of callsites to endpoints is
   *               justified by our desire to optimize).
   *
   *   (c) a class C owning a closure-endpoint method isn't a delegating-closure itself
   *       (it's fine for C to be a traditional-closure or a non-closure).
   *
   * Beware
   * ------
   *
   *   (1) Not really an invariant but almost:
   *       "all instantiations of dclosure D are enclosed in a method of the master class of D"
   *       With inlining, "transplanting" a method's instructions to another class may break the property above.
   *
   *
   *   (2) Care is needed to preserve Invariant (b.2) in the presence of closure-inlining and delayedInit,
   *       ie we want to preserve:
   *             static-HiO's declaring class == master class of the inlined dclosure
   *
   *   (3) Just like with "traditional" anonymous closures, a dclosure may be instantiated
   *       at several program-points. This contradics what source-code suggests, and results
   *       from the way catch-clauses and finally-clauses are represented in bytecode
   *       (they are duplicated, one each for normal and exceptional control-flow,
   *       details in `GenBCode` in particular `genSynchronized()` , `genLoadTry()` , `emitFinalizer()`).
   *
   **/
  object closuRepo extends BCInnerClassGen {

    /**
     *  dclosure-class -> endpoint-as-methodRef-in-master-class
     *
     *  @see populateDClosureMaps() Before that method runs, this map is empty.
     */
    val endpoint = new java.util.concurrent.ConcurrentHashMap[BType, MethodRef]

    /**
     *  master-class -> dclosure-classes-it's-responsible-for
     *
     *  @see populateDClosureMaps() Before that method runs, this map is empty.
     */
    val dclosures = new java.util.concurrent.ConcurrentHashMap[BType, List[BType]]

    /**
     *  dclosure-class -> "classes other than its master-class referring to it, via NEW dclosure or INVOKE endpoint"
     *
     *  @see populateNonMasterUsers() Before that method runs, this map is empty.
     */
    val nonMasterUsers = mutable.Map.empty[BType, mutable.Set[BType]]

    def hasMultipleUsers(closuBT: BType): Boolean = {
      val others = nonMasterUsers.getOrElse(closuBT, null)

      (others != null) && others.nonEmpty
    }

    def isNonMasterUser(closuBT: BType, enclClass: BType): Boolean = {
      val others = nonMasterUsers.getOrElse(closuBT, null)

      (others != null) && others.contains(enclClass)
    }

    def addAnotherUser(closuBT: BType, enclClass: BType) {
      val others = nonMasterUsers.getOrElse(closuBT, mutable.Set.empty)
      nonMasterUsers.put(closuBT, others += enclClass)
    }

    // --------------------- query methods ---------------------

    def isDelegatingClosure( c:    BType):     Boolean = { endpoint.containsKey(c) }
    def isDelegatingClosure(iname: String):    Boolean = { isDelegatingClosure(lookupRefBType(iname)) }
    def isDelegatingClosure(cnode: ClassNode): Boolean = { isDelegatingClosure(cnode.name) }

    def isTraditionalClosure(c: BType): Boolean = { c.isClosureClass && !isDelegatingClosure(c) }

    def masterClass(dclosure: BType): BType = { endpoint.get(dclosure).ownerClass }

    def isMasterClass(c:     BType ):    Boolean = { dclosures.containsKey(c) }
    def isMasterClass(iname: String):    Boolean = { isMasterClass(lookupRefBType(iname)) }
    def isMasterClass(cnode: ClassNode): Boolean = { isMasterClass(cnode.name) }

    /**
     * The set of delegating-closures created during UnCurry, represented as BTypes.
     * Some of these might not be emitted, e.g. as a result of dead-code elimination or closure inlining.
     * */
    def allDClosures:     collection.Set[BType] = { JSetWrapper(endpoint.keySet)  }
    def allMasterClasses: collection.Set[BType] = { JSetWrapper(dclosures.keySet) }

    /**
     * The set of delegating-closures used by no other class than the argument
     * (besides the trivial usage of each dclosure by itself).
     * */
    def exclusiveDClosures(master: BType): List[BType] = {
      dclosures.get(master) filter { dc => !hasMultipleUsers(dc) }
    }

    def isDClosureExclusiveTo(d: BType, master: BType): Boolean = {
      exclusiveDClosures(master) contains d
    }

    /**
     * The set of delegating-closures used by no other class than the argument
     * (besides the trivial usage of each dclosure by itself)
     * and moreover not elided (as a consequence, endpoint is public).
     * */
    def liveDClosures(masterCNode: ClassNode): List[BType] = {
      val masterBT = lookupRefBType(masterCNode.name)
      assert(isMasterClass(masterBT), "Not a master class for any dclosure: " + masterBT.getInternalName)
      for(
        d <- exclusiveDClosures(masterBT);
        if !elidedClasses.contains(d);
        dep = endpoint.get(d).mnode;
        // looking ahead, it's possible for the static endpoint of a dclosure to be inlined into the dclosure's apply().
        if masterCNode.methods.contains(dep)
      ) yield d
    }

    def closureInstantiations(mnode: MethodNode, dclosure: BType): List[AbstractInsnNode] = {
      assert(dclosure != null)
      mnode.instructions.toList filter { insn => instantiatedDClosure(insn) == dclosure }
    }

    def closureInvocations(mnode: MethodNode, dclosure: BType): List[AbstractInsnNode] = {
      assert(dclosure != null)
      mnode.instructions.toList filter { insn => invokedDClosure(insn) == dclosure }
    }

    def closureAccesses(mnode: MethodNode, dclosure: BType): List[AbstractInsnNode] = {
      assert(dclosure != null)
      mnode.instructions.toList filter { insn => accessedDClosure(insn) == dclosure }
    }

    // ------------------------------- yes/no inspectors and asserts ------------------------------

    /**
     *  A master-class of a non-elided dclosure contains:
     *    - a single instantiation of it, and
     *    - no invocations to the dclosure's endpoint.
     *  (the "non-elided" part is responsible for that property: a dclosure that was inlined
     *   has a callsite to the endpoint in the shio method that replaces the higher-order method invocation).
     * */
    def assertEndpointInvocationsIsEmpty(masterCNode: ClassNode, dclosure: BType) {
      for( /*debug*/
        masterMethod <- JListWrapper(masterCNode.methods);
        if !Util.isAbstractMethod(masterMethod)
      ) {
        assert(
          closuRepo.closureInvocations(masterMethod, dclosure).isEmpty,
          "A master class of a non-elided dclosure is supposed to contain a single instantiation of it, however " +
         s"${methodSignature(masterCNode, masterMethod)} invokes the endpoint of ${dclosure.getInternalName}"
        )
      }
    }

    // -------------- utilities to track dclosure usages in classes other than master --------------

    /**
     * Matches a "NEW dclosure" instruction returning the dclosure's BType in that case. Otherwise null.
     * */
    private def instantiatedDClosure(insn: AbstractInsnNode): BType = {
      if(insn.getOpcode == Opcodes.NEW) {
        val ti  = insn.asInstanceOf[TypeInsnNode]
        val dbt = lookupRefBType(ti.desc)
        if(isDelegatingClosure(dbt)) {
          return dbt
        }
      }

      null
    }

    /**
     * Matches a "INVOKE dclosure-endpoint" instruction returning the dclosure's BType in that case. Otherwise null.
     * */
    def invokedDClosure(insn: AbstractInsnNode): BType = {
      if(insn.getType == AbstractInsnNode.METHOD_INSN) {
        val mi     = insn.asInstanceOf[MethodInsnNode]
        val master = lookupRefBType(mi.owner)
        if(isMasterClass(master)) {
          for(
            dclosure <- dclosures.get(master);
            mnode: MethodNode = endpoint.get(dclosure).mnode;
            if (mnode.name == mi.name) && (mnode.desc == mi.desc)
          ) {
            return dclosure
          }
        }
      }

      null
    }

    /**
     * Matches a dclosure instantiation or endpoint invocation, returning the dclosure's BType in that case. Otherwise null.
     * */
    private def accessedDClosure(insn: AbstractInsnNode): BType = {
      instantiatedDClosure(insn) match {
        case null => invokedDClosure(insn)
        case dc   => dc
      }
    }

    /**
     *  In case `insn` denotes a dclosure instantiation or endpoint invocation lexically enclosed in `enclClass`
     *  and `enclClass` isn't the master class of that closure, note this fact `nonMasterUsers`.
     *
     *  Motivation
     *  ----------
     *
     *  Right after GenBCode, each "NEW dclosure" instruction is enclosed by masterClass(dclosure).
     *
     *      Sidenote of historic interest: in the past, the rewriting for DelayedInit
     *      resulted in exceptions to the above, but currently
     *      (see `delayedEndpointDef()` in `ConstructorTransformer`)
     *      that's not the case anymore.
     *
     *  However, non-master-class usages of dclosures may result from inlining.
     *  Given that this method takes note of those usages, after `WholeProgramAnalysis.optimize()` has run
     *  we know where to look for usages of a given dclosure.
     *
     *  Knowing "all classes enclosing usages of a dclosure" is needed to partition the set of dclosures
     *  so that different Worker2 threads have exclusive access to different partitions.
     *  Why? Because when performing dclosure optimizations, a limited form of inter-class mutations are done
     *  (for example, to minimize closure state).
     *
     *  @param insn      bytecode instruction that may access a dclosure
     *  @param enclClass enclosing class where the usage of the dclosure appears
     *
     * */
    def trackClosureUsageIfAny(insn: AbstractInsnNode, enclClass: BType) {
      val dc = accessedDClosure(insn)
      if(dc == null || enclClass == dc || !isDelegatingClosure(dc)) { return }
      assert(
        !isDelegatingClosure(enclClass),
         "A dclosure D is used by a class C other than its master class, but C is a dclosure itself. " +
        s"Who plays each role: D by ${dc.getInternalName} , C by ${enclClass.getInternalName} "
      )
      if(enclClass != masterClass(dc)) {
        addAnotherUser(dc, enclClass)
      }
    }

    // --------------------- closuRepo initializers ---------------------

    /**
     *  Checks about usages of dclosures.
     *
     *  Before the Inliner has run, a dclosure:
     *
     *    (a) may be instantiated only in its master class (if at all).
     *        In case dead-code elimination has run, a dclosure might not be instantiated at all,
     *        not even in its master class.
     *
     *    (b) may have its endpoint invoked only in the dclosure class itself.
     *
     *  In addition to the above, after the Inliner has run, a dclosure may also
     *
     *    (c) be instantiated in a nonMasterUser,
     *    (d) have its endpoint invoked by its masterClass or a nonMasterUser.
     *
     * */
    def checkDClosureUsages(enclClassCN: ClassNode) {

      val enclClassBT = lookupRefBType(enclClassCN.name)
      for(
        mnode <- JListWrapper(enclClassCN.methods);
        if !Util.isAbstractMethod(mnode)
      ) {
        mnode foreachInsn { insn =>

          // properties (a) , (c)
          var dc: BType = instantiatedDClosure(insn)
          assert(
            dc == null ||
            enclClassBT == masterClass(dc) ||
            (isInliningDone && isNonMasterUser(dc, enclClassBT)),
             "A dclosure D is instantiated by a class C other than its master class, and " +
             "inlining + nonMasterUsers doesn't explain it either. " +
            s"Who plays each role: D by ${dc.getInternalName} , its master class is ${masterClass(dc).getInternalName} , " +
            s"and the enclosing class is ${enclClassBT.getInternalName} "
          )

          // properties (b) , (d)
          dc = invokedDClosure(insn)
          assert(
            dc == null ||
            enclClassBT == dc ||
            (isInliningDone && (enclClassBT == masterClass(dc) || isNonMasterUser(dc, enclClassBT))),
            "A dclosure D is has its endpoint invoked by a class C other than D itself, and " +
            "inlining + nonMasterUsers doesn't explain it either. " +
           s"Who plays each role: D by ${dc.getInternalName} , and the enclosing class is ${enclClassBT.getInternalName} "
          )

        }
      }
    }

    /**
     *  @see checkDClosureUsages(enclClassCN: ClassNode)
     * */
    def checkDClosureUsages() {

      assert(if(!isInliningDone) nonMasterUsers.isEmpty else true)

      val iterCompiledEntries = codeRepo.classes.entrySet().iterator()
      while(iterCompiledEntries.hasNext) {
        val e = iterCompiledEntries.next()
        val enclClassCN: ClassNode = e.getValue
        checkDClosureUsages(enclClassCN)
      }

    }

    // --------------------- closuRepo post-initialization utilities ---------------------

    /**
     *  TODO Confirm no unwanted interaction when multiple usages are present in master class (due to duplication of catch and finally clauses)
     *       Eliding only possible when no instantiation-usages present.
     * */
    def retractAsDClosure(dc: BType) {
      assert(
        !hasMultipleUsers(dc),
        s"A dclosure can't be retracted unless used only by its master class, but ${dc.getInternalName} in use by ${nonMasterUsers(dc).mkString}"
      )
      val exMaster = masterClass(dc)
      endpoint.remove(dc)
      if(dclosures.containsKey(exMaster)) {
        val other = dclosures.get(exMaster) filterNot { _ == dc }
        if(other.isEmpty) { dclosures.remove(exMaster)     }
        else              { dclosures.put(exMaster, other) }
      }
    }

    def clear() {
      uncurry.closureDelegates.clear()
      endpoint.clear()
      dclosures.clear()
      nonMasterUsers.clear()
    }

  } // end of object closuRepo

  //---------------------------------------------------------------------------
  // Optimization pack: closures (located here due to proximity with closuRepo)
  //---------------------------------------------------------------------------

  final class DClosureOptimizerImpl(masterCNode: ClassNode) {

    val masterBT = lookupRefBType(masterCNode.name)
    assert(
      closuRepo.isMasterClass(masterBT),
      "A dclosure optimmizer was instantiated for a class lacking dclosures: " + masterBT.getInternalName
    )

    val staticMaker = new asm.optimiz.StaticMaker

    /**
     * Focuses on those dclosures that the `cnode` argument is exclusively responsible for
     * (consequence: all usages of the dclosure are confined to two places: cnode and the dclosure itself).
     *
     * For each such closure:
     *
     *   (1) lack of usages in `cnode` (eg as a result of dead-code elimination) means the closure can be elided,
     *       along with its endpoint. This may lead to further tree-shaking in `cnode` (via UnusedPrivateDetector).
     *
     *   (2) minimize the dclosure fields (in particular, outer) to those actually used.
     *       "Minimizing the outer instance" means the endpoint is made static.
     *       The dclosure itself remains, but with smaller GC overhead.
     *
     * This method can be run on the ClassNode of a Serializable class:
     * only isLiftedMethods or dclosure-endpoints will be mutated.
     *
     * */
    def shakeAndMinimizeClosures(): Boolean = {

      do { } while (!staticMaker.transform(masterCNode).isEmpty)

      val tooManyMethodsToScan = (masterCNode.methods.size() > 100) // otherwise files/run/bridges.scala takes unbelievably long to complete.

      var changed = false
      for(d <- closuRepo.liveDClosures(masterCNode)) {

        val dep = closuRepo.endpoint.get(d).mnode
        // if d not in use anymore (e.g., due to dead-code elimination) then remove its endpoint, and elide the class.
        val unused =
          !tooManyMethodsToScan &&
          { JListWrapper(masterCNode.methods) forall { mnode => closuRepo.closureAccesses(mnode, d).isEmpty } }
        if(unused) {
          changed = true
          elidedClasses.add(d) // a concurrent set
          masterCNode.methods.remove(dep)
          /* At this point we should closuRepo.retractAsDClosure(d) but the supporting maps aren't concurrent,
           * and moreover all three of them should be updated atomically. Relying on elidedClasses is enough. */
        }
        else if (!Util.isStaticMethod(dep)) {
          // the dclosure remains in use in cnode (it wasn't elided). The endpoint must still be there.
          assert(masterCNode.methods.contains(dep))
          assert(Util.isPublicMethod(dep))
          changed |= minimizeDClosureFields(dep, d)
        }

      }

      changed
    }

    /**
     * All usages of the dclosure are confined to two places: its master class and the dclosure itself.
     * We can minimize dclosure fields (in particular, outer) because we know where to find
     * all of the (dclosure instantiations, endpoint invocations) that will require adapting to remain well-formed.
     *
     * */
    private def minimizeDClosureFields(endpoint: MethodNode, d: BType): Boolean = {
      import asm.optimiz.UnusedParamsElider
      import asm.optimiz.StaticMaker

      assertPipeline1Done(
        "This optimization might register a yet unseen method descriptor. Before doing so, global is locked." +
        "For that to work, pipeline-1 must have completed (because Worker1 registers itselfs new BTypes, without locking)."
      )

      val dCNode: ClassNode = codeRepo.classes.get(d)

          /**
           *  (1) remove params that go unused at the endpoint in the master class,
           *      also removing the arguments provided by the callsite in the dclosure class.
           *
           *  (2) attempt to make static the endpoint (and its invocation).
           *
           *  A master-class of a non-elided dclosure contains:
           *    - one or more instantiations of it ("or more" because of duplication of catch and try clauses), and
           *    - no invocations to the dclosure's endpoint
           *     (the "non-elided" part is responsible for "no invocations to the dclosure's endpoint":
           *      a dclosure that was inlined has a callsite to the endpoint in the shio method
           *      that replaces the higher-order method invocation).
           *
           * */
          def adaptEndpointAndItsCallsite(): Boolean = {
            var changed  = false
            val oldDescr = endpoint.desc
            // don't run UnusedPrivateDetector on a ClassNode with a method temporarily made private.
            Util.makePrivateMethod(endpoint) // temporarily

            val elidedParams: java.util.Set[java.lang.Integer] = UnusedParamsElider.elideUnusedParams(masterCNode, endpoint)
            if(!elidedParams.isEmpty) {
              changed = true
              global synchronized {
                BType.getMethodType(endpoint.desc)
              }
              log(
               s"In order to minimize closure-fields, one or more params were elided from endpoint ${methodSignature(masterCNode, endpoint)} " +
               s". Before the change, its method descriptor was $oldDescr"
              )
              for(dmethod <- JListWrapper(dCNode.methods)) {
                UnusedParamsElider.elideArguments(dCNode, dmethod, masterCNode, endpoint, oldDescr, elidedParams)
              }
              closuRepo.assertEndpointInvocationsIsEmpty(masterCNode, d) /*debug*/
            }

            if(Util.isInstanceMethod(endpoint) && StaticMaker.lacksUsagesOfTHIS(endpoint)) {
              changed = true
              log(s"In order to minimize closure-fields, made static endpoint ${methodSignature(masterCNode, endpoint)}")
              Util.makeStaticMethod(endpoint)
              StaticMaker.downShiftLocalVarUsages(endpoint)
              for (dmethod <- JListWrapper(dCNode.methods)) {
                assert(!Util.isAbstractMethod(dmethod))
                StaticMaker.adaptCallsitesTargeting(dCNode, dmethod, masterCNode, endpoint)
              }
              closuRepo.assertEndpointInvocationsIsEmpty(masterCNode, d) /*debug*/
            }

            Util.makePublicMethod(endpoint)

            changed
          }

      if(!adaptEndpointAndItsCallsite()) {
        return false
      }

      // past this point one or more closure-fields are to be elided (outer instance, captured local, or any combination thereof).

      // PUTFIELD instructions for dclosure-fields that are never read can be eliminated,
      // which in turn is a pre-requisite for removal of redundant closure-state fields.
      // The whole process involves several steps.

      /*
       * Step 1: cancel-out DROP of closure-state GETFIELD
       * -------------------------------------------------
       *
       * Even if PushPopCollapser is run on the dclosure, instruction pairs of the form:
       *   LOAD_0
       *   GETFIELD of a closure-field
       *   DROP
       * still remain (PushPopCollapser does not elide a GETFIELD of a private final field,
       * because it doesn't check whether it's been assigned already or not).
       *
       * The custom transform below gets rid of those GETFIELD instructions, rewriting the above into:
       *   LOAD_0
       *   DROP
       *
       * A follow-up round of PushPopCollapser finishes the code clean-up.
       * */
      val cp = ProdConsAnalyzer.create()
      for (caller <- JListWrapper(dCNode.methods)) {
        Util.computeMaxLocalsMaxStack(caller)
        cp.analyze(dCNode.name, caller)
        for(
          // we'll modify caller.instructions in the for-body, that's fine because toList returns another list.
          drop <- caller.instructions.toList;
          if Util.isDROP(drop);
          producers = cp.producers(drop);
          if producers.size() == 1;
          prod = producers.iterator().next;
          if prod.getOpcode == Opcodes.GETFIELD;
          if prod.asInstanceOf[FieldInsnNode].owner == dCNode.name;
          if cp.isPointToPoint(prod, drop)
        ) {
          caller.instructions.set(prod, Util.getDrop(1)) // drop the receiver of GETFIELD, ie drop the result of LOAD_0
          caller.instructions.remove(drop)               // cancel-out the DROP for the result of GETFIELD
        }
      }

      val cleanser = createBCodeCleanser(dCNode, false)
      cleanser.intraMethodFixpoints(full = false)

      /*
       * Step 2: determine (declared) `closureState` and (effectively used) `whatGetsRead`
       * ---------------------------------------------------------------------------------
       * */
      val closureState: Map[String, FieldNode] = {
        JListWrapper(dCNode.fields).toList filter { fnode => Util.isInstanceField(fnode) } map { fnode => (fnode.name -> fnode) }
      }.toMap
      val whatGetsRead = mutable.Set.empty[String]
      for(
        caller <- JListWrapper(dCNode.methods);
        insn   <- caller.instructions.toList
      ) {
        if (insn.getOpcode == Opcodes.GETFIELD) {
          val fieldRead = insn.asInstanceOf[FieldInsnNode]
          assert(fieldRead.owner == dCNode.name)
          if (closureState.contains(fieldRead.name)) {
            whatGetsRead += fieldRead.name
          }
        }
      }

      if(whatGetsRead.size == closureState.size) {
        // elidedParams may refer to an apply-arg or a captured local, or combination thereof.
        return true // no closure-state field to elide after all (e.g., outer was a module, see test/files/run/Course-2002-10.scala)
      }

      val fieldsToRemove = for(Pair(fname, fnode) <- closureState; if !whatGetsRead.contains(fname) ) yield fnode;
      log(
       s"Minimizing closure-fields in dclosure ${d.getInternalName}. The following fields will be removed " +
       (fieldsToRemove map { fnode => fnode.name + " : " + fnode.desc }).mkString
      )

      /*
       * Step 3: determine correspondence redundant-closure-field-name -> constructor-params-position
       * --------------------------------------------------------------------------------------------
       * */
      // redundant-closure-field-name -> zero-based position the constructor param providing the value for it.
      val posOfRedundantCtorParam = mutable.Map.empty[String, Int]
      val ctor = (JListWrapper(dCNode.methods) find { caller => caller.name == "<init>" }).get
      val ctorBT = BType.getMethodType(ctor.desc)
      Util.computeMaxLocalsMaxStack(ctor)
      cp.analyze(dCNode.name, ctor)
      for(
        insn   <- ctor.instructions.toList
      ) {
        if (insn.getOpcode == Opcodes.PUTFIELD) {
          val fieldWrite = insn.asInstanceOf[FieldInsnNode]
          assert(fieldWrite.owner == dCNode.name)
          if (!whatGetsRead.contains(fieldWrite.name)) {
            val nonThisLocals = {
              JSetWrapper(cp.producers(fieldWrite)) map { insn => insn.asInstanceOf[VarInsnNode].`var` } filterNot { _ == 0 }
            }
            assert(nonThisLocals.size == 1)
            assert(!posOfRedundantCtorParam.contains(fieldWrite.name))
            val localVarIdx = nonThisLocals.iterator.next
            val paramPos    = ctorBT.convertLocalVarIdxToFormalParamPos(localVarIdx, true)
            posOfRedundantCtorParam.put(fieldWrite.name, paramPos)
          }
        }
      }
      assert(posOfRedundantCtorParam.nonEmpty)

      val isOuterRedundant = {
         closureState.contains(nme.OUTER.toString) &&
        !whatGetsRead.contains(nme.OUTER.toString)
      }

      /*
       * Step 4: in the dclosure (e.g. its constructor) get rid of PUTFIELDs to closure-state fields never read
       * ------------------------------------------------------------------------------------------------------
       * */
      for(
        caller <- JListWrapper(dCNode.methods);
        insn   <- caller.instructions.toList
      ) {
        if (insn.getOpcode == Opcodes.PUTFIELD) {
          val fieldWrite = insn.asInstanceOf[FieldInsnNode]
          assert(fieldWrite.owner == dCNode.name)
          if (!whatGetsRead.contains(fieldWrite.name)) {
            val fnode = closureState(fieldWrite.name)
            val size  = descrToBType(fnode.desc).getSize
            caller.instructions.insert(fieldWrite, Util.getDrop(1)) // drops THIS
            caller.instructions.set(fieldWrite, Util.getDrop(size)) // drops field value
          }
        }
      }

      /*
       * Step 5: back-propagate DROPs inserted above, and remove redundant fields
       * (otherwise another attempt will be made to delete them next time around)
       * ------------------------------------------------------------------------
       * */
      cleanser.intraMethodFixpoints(full = false)
      for(fnode <- closureState.values; if !whatGetsRead.contains(fnode.name)) {
        dCNode.fields.remove(fnode)
      }

      /*
       * Step 6: adapt the method descriptor of the dclosure constructor, as well as <init> callsite in master class
       * -----------------------------------------------------------------------------------------------------------
       * */
      Util.makePrivateMethod(ctor) // temporarily
      val oldCtorDescr = ctor.desc
      val elideCtorParams: java.util.Set[java.lang.Integer] = UnusedParamsElider.elideUnusedParams(dCNode, ctor)
      Util.makePublicMethod(ctor)
      global synchronized {
        BType.getMethodType(ctor.desc)
      }
      assert(!elideCtorParams.isEmpty)
      for(callerInMaster <- JListWrapper(masterCNode.methods)) {
        UnusedParamsElider.elideArguments(masterCNode, callerInMaster, dCNode, ctor, oldCtorDescr, elideCtorParams)
      }

      true
    } // end of method minimizeDClosureFields()

    /**
     * Once no further `minimizeDClosureFields()` is possible, dclosures can be partitioned into the following classes:
     *
     *   (1) empty closure state: the endpoint (necessarily a static method) is invoked with (a subset of) the apply()'s arguments.
     *       In this case the closure can be turned into a singleton.
     *
     *   (2) closure state consisting only of outer-instance: irrespective of the dclosure's arity,
     *       besides (a subset of) the apply()'s arguments, the only additional value needed
     *       to invoke the endpoint is the outer-instance value.
     *       In this case the closure can be allocated once per outer-instance
     *       (for example, in the constructor of the class of the outer instance).
     *       "Per-outer-instance closure-singletons" are a trade-off: the assumption being their instantiation
     *       will be amortized over the many times it's passed as argument.
     *
     *   (3) closure state consists of one or more values other than the outer instance, if any.
     *
     *       In other words the subcases are:
     *         (3.a) the outer-instance and one or more captured values, or
     *         (3.b) one or more captured values,
     *       constitute the closure state.
     *       Under (3.a) the endpoint is an instance-method, while for (3.b) it's static.
     *
     *       In this last case (3), an allocation is needed each time the closure is passed as argument (to convey those captured values).
     *
     *       In theory two closures of the same closure-class capturing the same values are inter-changeable,
     *       thus a runtime "dictionary lookup" could provide an existing closure instance for a given tuple of captured values. Expensive.
     *
     * */
    def minimizeDClosureAllocations() {
      singletonizeDClosures()         // Case (1) empty closure state
    }

    /**
     *  Handle the following subcase described in minimizeDClosureAllocations():
     *
     *   (1) empty closure state: the endpoint (necessarily a static method) is invoked with (a subset of) the apply()'s arguments.
     *       In this case the closure can be turned into a singleton.
     *
     *  The `singletonize()` optimization involves adding a class-initializer
     *  (aka <clinit> , static constructor) to the Late-Closure-Class.
     *  In the Java language, "Inner classes may not declare static initializers or member interfaces." (JLS, Java 7 Edition, Sec. 8.1.3)
     *  However that's not a JVM restriction.
     *
     * */
    private def singletonizeDClosures() {
      for(d <- closuRepo.liveDClosures(masterCNode)) {

        val dep    = closuRepo.endpoint.get(d).mnode
        val dCNode = codeRepo.classes.get(d)
        val closureState: Map[String, FieldNode] = {
          JListWrapper(dCNode.fields).toList filter { fnode => Util.isInstanceField(fnode) } map { fnode => (fnode.name -> fnode) }
        }.toMap
        val dClassDescriptor = "L" + dCNode.name + ";"

        // ------------------------------------------------------------------
        // Case (1): the dclosure can be turned into a program-wide singleton
        // ------------------------------------------------------------------
        val lacksClosureState = closureState.isEmpty
        if(lacksClosureState) {

          log("Singleton-closure: " + dCNode.name)

          // -------- (1.a) modify the dclosure class (add $single static field, initialize it in <clinit>)
          val ctor = (JListWrapper(dCNode.methods) find { caller => caller.name == "<init>" }).get
          Util.makePrivateMethod(ctor)
          val single =
            new FieldNode(
              Opcodes.ASM4,
              Opcodes.ACC_PUBLIC | Opcodes.ACC_FINAL | Opcodes.ACC_STATIC,
              "$single",
              dClassDescriptor,
              null, null
            )
          dCNode.fields.add(single)
          val staticClassInitializer =
            new MethodNode(
              Opcodes.ASM4,
              Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC,
              "<clinit>",
              "()V",
              null, null
            )
          dCNode.methods.add(staticClassInitializer)
          val insns = new InsnList()
          insns.add(new TypeInsnNode(Opcodes.NEW, dCNode.name))
          insns.add(new InsnNode(Opcodes.DUP))
          insns.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, dCNode.name, "<init>", "()V"))
          insns.add(new FieldInsnNode(Opcodes.PUTSTATIC, dCNode.name, single.name, dClassDescriptor))
          insns.add(new InsnNode(Opcodes.RETURN))
          staticClassInitializer.instructions.add(insns)

          // -------- (1.b) modify the master class (replace instantiation by GETSTATIC of the singleton)
          for(
            callerInMaster <- JListWrapper(masterCNode.methods);
            newInsn        <- closuRepo.closureAccesses(callerInMaster, d)
          ) {
            assert(newInsn.getOpcode == Opcodes.NEW)
            /*
             * A dclosure instantiation (the code pattern to replace) usually looks like:
             *
             *     NEW dclosure
             *     DUP
             *     INVOKESPECIAL dclosure.<init> ()V
             *
             * In a few cases it may look like:
             *
             *     NEW dclosure
             *     DUP
             *     ALOAD 0
             *     CHECKCAST X
             *     POP
             *     INVOKESPECIAL dclosure.<init> ()V
             *
             * The second case arises because PushPopCollapser doesn't back-propagate POP over CHECKCAST
             * (that would requires a type-flow based analysis).
             *
             * */

                def snippetTest(idx: Int, insn: AbstractInsnNode, pf: PartialFunction[AbstractInsnNode, Boolean]): Boolean = {
                  val isBoilerplate = pf.isDefinedAt(insn) && pf(insn)
                  if(!isBoilerplate) {
                    log(
                      s"Attempt to replace instantiation with GETSTATIC of singleton dclosure ${d.getInternalName} " +
                      s"in method ${methodSignature(masterCNode, callerInMaster)}."  +
                      s"Expected another instruction at index ${callerInMaster.instructions.indexOf(insn)} but found ${Util.textify(insn)}\n." +
                       "Here's the complete bytecode of that method:" + Util.textify(callerInMaster)
                    )
                  }

                  isBoilerplate
                }

            val isLasInsnInBoilerplate: PartialFunction[AbstractInsnNode, Boolean] =
              { case mi: MethodInsnNode =>
                  mi.getOpcode == Opcodes.INVOKESPECIAL &&
                  mi.owner     == d.getInternalName     &&
                  mi.name      == "<init>" &&
                  mi.desc      == "()V"
                case _ => false
              }

                // logs only the first divergence from "boilerplate"
                def isBoilerplate = {
                  snippetTest(0, newInsn,         { case ti: TypeInsnNode   => ti.getOpcode == Opcodes.NEW && ti.desc == d.getInternalName }) &&
                  snippetTest(1, newInsn.getNext, { case di: InsnNode       => di.getOpcode == Opcodes.DUP }) &&
                  snippetTest(2, newInsn.getNext.getNext, isLasInsnInBoilerplate)
                }

            val lastInsn: MethodInsnNode = {
              var current: AbstractInsnNode = newInsn
              while(!isLasInsnInBoilerplate(current)) {
                current = current.getNext
              }
              current.asInstanceOf[MethodInsnNode]
            }

            if(!isBoilerplate) {
              val dupInsn = newInsn.getNext
              assert(dupInsn.getOpcode == Opcodes.DUP)
              // move NEW, DUP right before INVOKESPECIAL <init> , ie right before `lastInsn` of the instruction bracket
              callerInMaster.instructions.remove(newInsn)
              callerInMaster.instructions.remove(dupInsn)
              callerInMaster.instructions.insertBefore(lastInsn, newInsn)
              callerInMaster.instructions.insertBefore(lastInsn, dupInsn)
              assert(isBoilerplate)
            }

            // remove all instructions of the bracket except for the first one, NEW dclosure
            var current: AbstractInsnNode = lastInsn
            while(current ne newInsn) {
              val prev = current.getPrevious
              callerInMaster.instructions.remove(current)
              current = prev
            }
            // replace NEW dclosure by GETSTATIC singleton
            callerInMaster.instructions.set(
              newInsn,
              new FieldInsnNode(Opcodes.GETSTATIC, d.getInternalName, single.name, single.desc)
            )
          }

        }

      }

    } // end of method singletonizeDClosures()

  } // end of class DClosureOptimizerImpl

  /**
   * @param mnode a MethodNode, usually found via codeRepo.getMethod(bt: BType, name: String, desc: String)
   * @param owner ClassNode declaring mnode
   */
  case class MethodNodeAndOwner(mnode: MethodNode, owner: ClassNode) {
    assert(owner.methods.contains(mnode))
  }

  //--------------------------------------------------------
  // helpers to produce logging messages
  //--------------------------------------------------------

  final def methodSignature(ownerIName: String, methodName: String, methodDescriptor: String): String = {
    ownerIName + "::" + methodName + methodDescriptor
  }

  final def methodSignature(ownerBT: BType, methodName: String, methodDescriptor: String): String = {
    methodSignature(ownerBT.getInternalName, methodName, methodDescriptor)
  }

  final def methodSignature(ownerBT: BType, methodName: String, methodType: BType): String = {
    methodSignature(ownerBT.getInternalName, methodName, methodType.getDescriptor)
  }

  final def methodSignature(ownerIName: String, mnode: MethodNode): String = {
    methodSignature(ownerIName, mnode.name, mnode.desc)
  }

  final def methodSignature(ownerBT: BType, mnode: MethodNode): String = {
    methodSignature(ownerBT, mnode.name, mnode.desc)
  }

  final def methodSignature(cnode: ClassNode, mnode: MethodNode): String = {
    methodSignature(lookupRefBType(cnode.name), mnode.name, mnode.desc)
  }

  final def insnPos(insn: AbstractInsnNode, mnode: MethodNode): String = {
   s"${Util.textify(insn)} at index ${mnode.instructions.indexOf(insn)}"
  }

  final def insnPosInMethodSignature(insn: AbstractInsnNode, mnode: MethodNode, cnode: ClassNode): String = {
    insnPos(insn, mnode) + s" in method ${methodSignature(cnode, mnode)}"
  }

  final def insnPosInMethodSignature(insn: AbstractInsnNode, mnode: MethodNode, ownerIName: String): String = {
    insnPos(insn, mnode) + s" in method ${methodSignature(ownerIName, mnode)}"
  }

} // end of class BCodeOptCommon