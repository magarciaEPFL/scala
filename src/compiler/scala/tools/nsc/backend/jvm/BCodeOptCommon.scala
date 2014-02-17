/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import backend.bcode.Util
import asm.tree._

import scala.collection.{ mutable, immutable }

/*
 *  Utilities shared across intra-method and inter-procedural optimizations.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOptCommon extends BCodeHelpers {

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
  final def wasElided(bt:    BType)    : Boolean = elidedClasses.contains(bt)
  final def wasElided(iname: String)   : Boolean = wasElided(lookupRefBType(iname))
  final def wasElided(cnode: ClassNode): Boolean = wasElided(cnode.name)

  /*
   *  Single-access point for requests to parse bytecode for inlining purposes.
   *  Given the BType of a class with internal name,
   *  `codeRepo` allows obtaining its bytecode-level representation (ClassNode).
   *  It's possible to find out whether a ClassNode was compiled in this run, or parsed from an external library.
   */
  object codeRepo {

    val parsed  = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]
    val classes = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]

    def containsKey(bt: BType): Boolean = { classes.containsKey(bt) || parsed.containsKey(bt) }

    /*
     *  must-single-thread
     */
    def getFieldOrNull(bt: BType, name: String, desc: String): FieldNode = {
      try { getField(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the FieldInsnNode have compiled?
      }
    }

    /*
     *  must-single-thread
     */
    def getMethodOrNull(bt: BType, name: String, desc: String): MethodNodeAndOwner = {
      try { getMethod(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
    }

    /*
     *  @return None if not found, the MethodNode's access field otherwise.
     *
     *  must-single-thread
     *
     */
    def getMethodAccess(bt: BType, name: String, desc: String): Option[Int] = {
      val cn =
        try   { getClassNode(bt) }
        catch { case _: MissingRequirementError => return None }
      val iter = cn.methods.iterator()
      while (iter.hasNext) {
        val mn = iter.next()
        if (mn.name == name && mn.desc == desc) {
          return Some(mn.access)
        }
      }
      import scala.collection.JavaConverters._
      for(ifaceIName <- cn.interfaces.asScala) {
        val outcome = getMethodAccess(lookupRefBType(ifaceIName), name, desc)
        if (outcome.nonEmpty) { return outcome }
      }
      if (cn.superName != null) {
        val outcome = getMethodAccess(lookupRefBType(cn.superName), name, desc)
        if (outcome.nonEmpty) { return outcome }
      }
      None
    }

    /*
     * Looks up (parsing from bytecode if needed) the field declared in `bt`
     * given by the combination of field-name and field-descriptor.
     *
     * must-single-thread
     */
    def getField(bt: BType, name: String, desc: String): FieldNode = {
      val cn = getClassNode(bt)
      val iter = cn.fields.iterator()
      while (iter.hasNext) {
        val fn = iter.next()
        if (fn.name == name && fn.desc == desc) {
          return fn
        }
      }

      MissingRequirementError.notFound(s"Could not find FieldNode: ${bt.getInternalName}.$name: ${desc}")
    }

    /*
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

      while (current != null) {
        val cn = getClassNode(current)
        val iter = cn.methods.iterator()
        while (iter.hasNext) {
          val mn = iter.next()
          if (mn.name == name && mn.desc == desc) {
            return MethodNodeAndOwner(mn, cn)
          }
        }
        current = if (cn.superName == null) null else lookupRefBType(cn.superName)
      }

      MissingRequirementError.notFound(s"Could not find MethodNode: ${bt.getInternalName}.${name}${desc}")
    }

    /* must-single-thread */
    def getClassNode(owner: String): asm.tree.ClassNode = { getClassNode(brefType(owner)) }

    /*
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
      if (res == null) {
        res = parsed.get(bt)
        if (res == null) {
          res = parseClassAndEnterExemplar(bt)
        }
      }
      assert(exemplars.containsKey(bt))
      res
    }

    /*  can-multi-thread*/
    def getClassNodeOrNull(bt: BType): asm.tree.ClassNode = {
      var res = classes.get(bt)
      if (res == null) {
        res = parsed.get(bt)
        // we can't call parseClassAndEnterExemplar(bt) because in the time window from the checks above and
        // the time parseClassAndEnterExemplar() runs, Worker1 may have added to codeRepo.classes the class we didn't find.
        // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
      res
    }

    /*
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

      /* must-single-thread */
      def parseClass(): asm.tree.ClassNode = {
        assert(!containsKey(bt))
        val iname   = bt.getInternalName
        val dotName = iname.replace('/', '.')
        classPath.findSourceFile(dotName) match {
          case Some(classFile) =>
            val cn = new asm.tree.ClassNode()
            val cr = new asm.ClassReader(classFile.toByteArray)
            cr.accept(cn, asm.ClassReader.SKIP_FRAMES)
            removeLineNumberNodes(cn)
            parsed.put(bt, cn)
            cn
          case _ => MissingRequirementError.notFound(s"Could not find bytecode for $dotName")
        }
      }

      val cn = parseClass()

      if (exemplars.containsKey(bt)) {
        return cn // TODO check if superName, interfaces, etc agree btw cn and exemplar(bt)
      }

      def enterIfUnseen(iname: String): Tracked = {
        val bt = brefType(iname)
        var exempl = exemplars.get(bt)
        if (exempl == null) {
          parseClassAndEnterExemplar(bt) // recursive call
          exempl = exemplars.get(bt)
        }
        exempl
      }

      def enterIfUnseens(inames: java.util.List[String]): Array[Tracked] = {
        var ifaces: List[Tracked] = Nil
        val iter = inames.iterator()
        while (iter.hasNext) {
          ifaces ::= enterIfUnseen(iter.next())
        }
        if (ifaces.isEmpty) { EMPTY_TRACKED_ARRAY }
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
        import scala.collection.JavaConverters._

        ((cn.innerClasses.asScala) map (icn => (icn.name -> icn))).toMap
      }

      val isInnerClass = innerClassNode.contains(cn.name)
      val innersChain: Array[InnerClassEntry] =
        if (!isInnerClass) null
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
            if (keepGoing) {
              chain ::= toInnerClassEntry(innerClassNode(currentOuter))
            }
          } while (keepGoing)

          chain.toArray
        }

      val tr = Tracked(bt, cn.access, tsc, ifacesArr, innersChain)
      exemplars.put(tr.c, tr) // no counterpart in symExemplars, that's life.

      cn
    }

    /*
     * This method removes all `asm.tree.LineNumberNode` nodes from each method in the argument ClassNode.
     * On the other hand, LocalVariableNode's are parsed (because they indicate position relative to LabelNodes,
     * which is fine with inlining).
     *
     * A classfile parsed from an external libray was necessarily compiled from another compilation unit,
     * thus any line-number information in that classfile won't make sense in connection with any other `ClassNode.sourceFile`
     * (for example, the `ClassNode.sourceFile` where a method of `cn` is inlined.
     */
    def removeLineNumberNodes(instructions: InsnList) {
      val iter = instructions.iterator()
      while (iter.hasNext) {
        val insn = iter.next()
        if (insn.isInstanceOf[LineNumberNode]) {
          iter.remove()
        }
      }
    }

    def removeLineNumberNodes(cn: ClassNode) {
      for(mnode <- cn.toMethodList) {
        removeLineNumberNodes(mnode.instructions)
      }
    }

    def isDebugInfoConsistent(a: ClassNode, b: ClassNode): Boolean = (
      (a.sourceFile != null) && (b.sourceFile != null) && (a.sourceFile == b.sourceFile)
    )

    /*
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
    def registerUnseenTypeNames(mn: MethodNode) {

      def enterInternalName(iname: String) {
        var bt = brefType(iname)
        if (bt.isArray) {
          bt = bt.getElementType
        }
        if (bt.isNonSpecial && !exemplars.containsKey(bt)) {
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
            val mt = BMType(desc)
            enterDescr(mt.returnType.getDescriptor)
            for(argt <- mt.argumentTypes) {
              enterDescr(argt.getDescriptor)
            }
          case '[' =>
            val arrt = BT.getFieldType(desc)
            enterDescr(arrt.getComponentType.getDescriptor)
        }
      }

      val iter = mn.instructions.iterator()
      while (iter.hasNext) {
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

      val tcbIter = mn.tryCatchBlocks.iterator()
      while(tcbIter.hasNext) {
        val tcb = tcbIter.next()
        val exc = tcb.`type`
        if (exc != null) {
          enterInternalName(exc)
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

  /*
   *  @return the callee, for a MethodNodeInsn, represented as MethodRef. Otherwise null.
   */
  final def accessedMethodRef(insn: AbstractInsnNode): MethodRef = {
    insn match {
      case mi: MethodInsnNode =>
        val ownerBT = lookupRefBType(mi.owner)
        val mnode   = codeRepo.getMethod(ownerBT, mi.name, mi.desc).mnode
        MethodRef(ownerBT, mnode)
      case _ => null
    }
  }

  /*
   * Repository for Late-Closure-Classes.
   */
  object closuRepo extends BCInnerClassGen {

    /*
     *  dclosure-class -> endpoint-as-methodRef-in-master-class
     *
     *  @see populateDClosureMaps() Before that method runs, this map is empty.
     */
    val endpoint = new java.util.concurrent.ConcurrentHashMap[BType, MethodRef]

    /*
     *  master-class -> dclosure-classes-it's-responsible-for
     *
     *  @see populateDClosureMaps() Before that method runs, this map is empty.
     */
    val dclosures = new java.util.concurrent.ConcurrentHashMap[BType, List[BType]]

    /*
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

    def isTraditionalClosure(c: BType): Boolean = { isClosureClass(c) && !isDelegatingClosure(c) }

    def masterClass(dclosure: BType): BType = { endpoint.get(dclosure).ownerClass }

    def isMasterClass(c:     BType ):    Boolean = { dclosures.containsKey(c) }
    def isMasterClass(iname: String):    Boolean = { isMasterClass(lookupRefBType(iname)) }
    def isMasterClass(cnode: ClassNode): Boolean = { isMasterClass(cnode.name) }

    /*
     * The set of delegating-closures created during UnCurry, represented as BTypes.
     * Some of these might not be emitted, e.g. as a result of dead-code elimination or closure inlining.
     */
    def allDClosures:     collection.Set[BType] = { import scala.collection.JavaConverters._ ; endpoint.keySet.asScala  }
    def allMasterClasses: collection.Set[BType] = { import scala.collection.JavaConverters._ ; dclosures.keySet.asScala }

    /*
     * The set of delegating-closures used by no other class than the argument
     * (besides the trivial usage of each dclosure by itself).
     */
    def exclusiveDClosures(master: BType): List[BType] = {
      dclosures.get(master) filter { dc => !hasMultipleUsers(dc) }
    }

    def isDClosureExclusiveTo(d: BType, master: BType): Boolean = {
      exclusiveDClosures(master) contains d
    }

    /*
     * The set of delegating-closures used by no other class than the argument
     * (besides the trivial usage of each dclosure by itself)
     * and moreover not elided (as a consequence, endpoint is public).
     */
    def liveDClosures(masterCNode: ClassNode): List[BType] = {
      val masterBT = lookupRefBType(masterCNode.name)
      assert(isMasterClass(masterBT), s"Not a master class for any dclosure: ${masterBT.getInternalName}")
      for(
        d <- exclusiveDClosures(masterBT);
        if !wasElided(d);
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

    /*
     *  A master-class of a non-elided dclosure contains:
     *    - a single instantiation of it, and
     *    - no invocations to the dclosure's endpoint.
     *  (the "non-elided" part is responsible for that property: a dclosure that was inlined
     *   has a callsite to the endpoint in the shio method that replaces the higher-order method invocation).
     */
    def assertEndpointInvocationsIsEmpty(masterCNode: ClassNode, dclosure: BType) {
      for( /*debug*/
        masterMethod <- masterCNode.toMethodList;
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

    /*
     * Matches a "NEW dclosure" instruction returning the dclosure's BType in that case. Otherwise null.
     */
    private def instantiatedDClosure(insn: AbstractInsnNode): BType = {
      if (insn.getOpcode == asm.Opcodes.NEW) {
        val ti  = insn.asInstanceOf[TypeInsnNode]
        val dbt = lookupRefBType(ti.desc)
        if (isDelegatingClosure(dbt)) {
          return dbt
        }
      }

      null
    }

    /*
     * Matches a "INVOKE dclosure-endpoint" instruction returning the dclosure's BType in that case. Otherwise null.
     */
    def invokedDClosure(insn: AbstractInsnNode): BType = {
      if (insn.getType == AbstractInsnNode.METHOD_INSN) {
        val mi     = insn.asInstanceOf[MethodInsnNode]
        val master = lookupRefBType(mi.owner)
        if (isMasterClass(master)) {
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

    /*
     * Matches a "GETSTATIC singleton-dclosure" instruction returning the dclosure's BType in that case. Otherwise null.
     */
    private def getSingletonDClosure(insn: AbstractInsnNode): BType = {
      if (insn.getOpcode == asm.Opcodes.GETSTATIC) {
        val fi  = insn.asInstanceOf[FieldInsnNode]
        if (fi.name == "$single") {
          val dbt = lookupRefBType(fi.owner)
          if (isDelegatingClosure(dbt)) {
            return dbt
          }
        }
      }

      null
    }

    /*
     * Matches a dclosure instantiation or endpoint invocation, returning the dclosure's BType in that case. Otherwise null.
     */
    private def accessedDClosure(insn: AbstractInsnNode): BType = {
      var res = instantiatedDClosure(insn)
      if (res == null) {
        res = invokedDClosure(insn)
        if (res == null) {
          res = getSingletonDClosure(insn)
        }
      }
      res
    }

    /*
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
     */
    def trackClosureUsageIfAny(insn: AbstractInsnNode, enclClass: BType) {
      val dc = accessedDClosure(insn)
      if (dc == null || enclClass == dc || !isDelegatingClosure(dc)) { return }
      assert(
        !isDelegatingClosure(enclClass),
         "A dclosure D is used by a class C other than its master class, but C is a dclosure itself. " +
        s"Who plays each role: D by ${dc.getInternalName} , C by ${enclClass.getInternalName} "
      )
      if (enclClass != masterClass(dc)) {
        addAnotherUser(dc, enclClass)
      }
    }

    // --------------------- closuRepo initializers ---------------------

    /*
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
     */
    def checkDClosureUsages(enclClassCN: ClassNode) {

      val enclClassBT = lookupRefBType(enclClassCN.name)
      for(
        mnode <- enclClassCN.toMethodList;
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

    /*
     *  @see checkDClosureUsages(enclClassCN: ClassNode)
     */
    def checkDClosureUsages() {

      assert(if (!isInliningDone) nonMasterUsers.isEmpty else true)

      val iterCompiledEntries = codeRepo.classes.entrySet().iterator()
      while (iterCompiledEntries.hasNext) {
        val e = iterCompiledEntries.next()
        val enclClassCN: ClassNode = e.getValue
        checkDClosureUsages(enclClassCN)
      }

    }

    // --------------------- closuRepo post-initialization utilities ---------------------

    /*
     *  TODO Confirm no unwanted interaction when multiple usages are present in master class (due to duplication of catch and finally clauses)
     *       Eliding only possible when no instantiation-usages present.
     */
    def retractAsDClosure(dc: BType) {
      assert(
        !hasMultipleUsers(dc),
        s"A dclosure can't be retracted unless used only by its master class, but ${dc.getInternalName} in use by ${nonMasterUsers(dc).mkString}"
      )
      val exMaster = masterClass(dc)
      endpoint.remove(dc)
      if (dclosures.containsKey(exMaster)) {
        val other = dclosures.get(exMaster) filterNot { _ == dc }
        if (other.isEmpty) { dclosures.remove(exMaster)     }
        else               { dclosures.put(exMaster, other) }
      }
    }

    def clear() {
      endpoint.clear()
      dclosures.clear()
      nonMasterUsers.clear()
    }

  } // end of object closuRepo

  /*
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
