/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.{UnBoxAnalyzer, ProdConsAnalyzer, Util}
import asm.tree.analysis.SourceValue
import asm.tree._

import scala.collection.{ mutable, immutable }
import scala.Some
import collection.convert.Wrappers.JListWrapper
import collection.convert.Wrappers.JSetWrapper

/**
 *  Optimize and tidy-up bytecode before it's serialized for good.
 *  This class focuses on inter-procedural optimizations.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOptInter extends BCodeOptIntra {

  import global._

  val cgns = new mutable.PriorityQueue[CallGraphNode]()(cgnOrdering)

  /**
   * must-single-thread
   **/
  override def clearBCodeOpt() {
    super.clearBCodeOpt()
    cgns.clear()
    codeRepo.clear()
  }

  //--------------------------------------------------------
  // Optimization pack: Method-inlining and Closure-inlining
  //--------------------------------------------------------

  /**
   * Each MethodNode built for a plain class is inspected for callsites targeting @inline methods,
   * those callsites are collected in a `CallGraphNode` instance,
   * classified into "higher-order callsites" (ie taking one or more functions as arguments) and the rest.
   *
   * The callsites in question constitute "requests for inlining". An attempt will be made to fulfill them,
   * after breaking any inlining cycles. Moreover a request may prove unfeasible afterwards too,
   * e.g. due to the callsite program point having a deeper operand-stack than the arguments the callee expects,
   * and the callee contains exception handlers.
   *
   * A description of the workflow for method-inlining and closure-inlining can be found in `WholeProgramAnalysis.inlining()`.
   *
   * @param hostOwner the JVM-level class defining method host
   * @param host      the method were inlining has been requested
   *
   */
  final class CallGraphNode(val hostOwner: ClassNode, val host: MethodNode) {

    var hiOs:  List[InlineTarget] = Nil
    var procs: List[InlineTarget] = Nil

    def isEmpty    = (hiOs.isEmpty && procs.isEmpty)
    def candidates = (hiOs ::: procs).sorted(inlineTargetOrdering)

    /** can-multi-thread, provided each callsite.owner has been entered as TypeName in Names */
    def populate() {
      if(!Util.isReadyForAnalyzer(host)) {
        Util.computeMaxLocalsMaxStack(host)
      }
      for(c <- candidates) {
        val callsite = c.callsite
        val ownerBT = lookupRefBType(callsite.owner)
        // `null` usually indicates classfile wasn't found and thus couldn't be parsed. TODO warning?
        val mnAndOwner = codeRepo.getMethodOrNull(ownerBT, callsite.name, callsite.desc)
        c.setMethodAndOwner(mnAndOwner)
        if(c.callee != null && !Util.isReadyForAnalyzer(c.callee)) {
          Util.computeMaxLocalsMaxStack(c.callee)
        }
      }
      hiOs  = hiOs  filter { it => it.callee != null }
      procs = procs filter { it => it.callee != null }
    }

    def isRepOK: Boolean = {
      candidates forall { c => c.callee != host } // non-cyclic
    }

  }

  object cgnOrdering extends scala.math.Ordering[CallGraphNode] {
    def compare(x: CallGraphNode, y: CallGraphNode): Int = {
      var result = x.host.instructions.size().compare(y.host.instructions.size())
      if (result == 0) {
        result = x.hashCode().compare(y.hashCode())
      }
      result
    }
  }

  final class InlineTarget(val callsite: MethodInsnNode) {
    var callee: MethodNode = null
    var owner:  ClassNode  = null

    def setMethodAndOwner(mnAndOwner: MethodNodeAndOwner) {
      if(mnAndOwner == null) {
        callee = null
        owner  = null
      }
      else {
        callee = mnAndOwner.mnode
        owner  = mnAndOwner.owner
      }
    }
  }

  object inlineTargetOrdering extends scala.math.Ordering[InlineTarget] {
    def compare(x: InlineTarget, y: InlineTarget): Int = {
      x.hashCode().compare(y.hashCode())
    }
  }

  object codeRepo {

    val parsed  = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]
    val classes = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]

    def containsKey(bt: BType): Boolean = {
      val res = (classes.containsKey(bt) || parsed.containsKey(bt))

      res
    }

    def getFieldOrNull(bt: BType, name: String, desc: String): FieldNode = {
      try { getField(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the FieldInsnNode have compiled?
      }
    }

    def getMethodOrNull(bt: BType, name: String, desc: String): MethodNodeAndOwner = {
      try { getMethod(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
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

      MissingRequirementError.notFound("Could not find FieldNode: " + bt.getInternalName + "." + name + ": " + desc)
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

      MissingRequirementError.notFound("Could not find MethodNode: " + bt.getInternalName + "." + name + desc)
    }

    /** must-single-thread */
    def getClassNode(owner: String): asm.tree.ClassNode = {
      getClassNode(brefType(owner))
    }

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
     *  A few analyses (e.g., Type-Flow Analysis) require `exemplars` to contain entries for all classes the analysis encounters.
     *  A class that is being compiled is already associated to a Tracked instance (GenBCode took care of that).
     *  For a class `bt` mentioned in external bytecode, this method takes care of creating the necessary entry in `exemplars`.
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
      assert(bt.isNonSpecial,  "The `exemplars` map is supposed to hold ''normal'' classes only, not " + bt.getInternalName)
      assert(!containsKey(bt), "codeRepo already contains " + bt.getInternalName)

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
              case _ => MissingRequirementError.notFound("Could not find bytecode for " + dotName)
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
              parseClassAndEnterExemplar(bt)
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
     *  An invariant we want to maintain:
     *    "each internal name mentioned in an instruction that's part of this program
     *     should have a Tracked instance (which implies, a BType instance)"
     *  That invariant guarantees a Type-Flow Analysis can be run anytime, which might be useful.
     *
     *  This method goes over its argument looking for not-yet-seen TypeNames,
     *  fabricating a Tracked instance for them (if needed by parsing bytecode,
     *  thus the location of this method as utility in codeRepo).
     *
     *  Without a TypeName for an internal name or method descriptor, the following conversions can't be performed:
     *    from type-descriptor to BType, via `BCodeTypes.descrToBType()`
     *    from internal-name   to BType, via `BCodeTypes.lookupRefBType()`
     *  In turn, BTypes are indispensable as keys to the `exemplars` map.
     *
     *  must-single-thread
     */
    def enterExemplarsForUnseenTypeNames(insns: InsnList) {

        def enterInternalName(iname: String) {
          var bt = brefType(iname)
          if(bt.isArray) {
            bt = bt.getElementType
          }
          if(bt.isNonSpecial && !exemplars.containsKey(bt)) {
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

  /**
   * Whole-program analyses can be performed right after classfiles are in q2.
   * Before letting the intra-method optimizations loose on those classfiles
   * we do the inter-procedural optimizations.
   */
  class WholeProgramAnalysis {

    import asm.tree.analysis.{Analyzer, BasicValue, BasicInterpreter}

    /**
     *  Performs closure-inlining and method-inlining, by first breaking any cycles over the "inlined-into" relation (see `object dagset`).
     *  Afterwards, `inlineMethod(...)` takes care of method-inlining, and `inlineClosures(..)` of closure-inlining.
     */
    def inlining() {

      /*
       * The MethodNode for each callsite to an @inline method is found, if necessary by parsing bytecode
       * (ie the classfile given by a callsite's `owner` field).
       * Those classes can be parsed only after making sure they aren't being compiled in this run.
       * That's the case by now, in fact codeRepo.classes can't grow from now on.
       */
      val mn2cgn = mutable.Map.empty[MethodNode, CallGraphNode]
      for(cgn <- cgns) {
        cgn.populate()
        assert(cgn.isRepOK)
        mn2cgn += (cgn.host -> cgn)
      }
      /**
       *  Terminology:
       *    - host:   a method containing callsites for inlining
       *    - target: the method given by a callsite for inlining
       *
       *  `dagset` represents a set of DAGs with edges (target -> host)
       *  resulting from:
       *    (1) visiting all (host, targets) pairs collected during `GenBCode` in `BCodeOpt.cgns`,
       *    (2) adding to `dagset` a (target -> host) link unless doing so would establish a cycle.
       *
       *  Failure to add a link in (2) implies that `target` can't be inlined in `host`,
       *  thus the corresponding `InlineTarget` is removed from the `CallGraphNode` under consideration.
       *
       */
      object dagset extends mutable.HashMap[MethodNode, mutable.Set[MethodNode]] {

        /** true iff a link (target -> host) was added, false otherwise. */
        def linkUnlessCycle(target: MethodNode, host: MethodNode): Boolean = {
          val createsCycle = (this.contains(target) && isReachableFrom(target, host))
          val okToAdd = !createsCycle
          if(okToAdd) {
            val hosts = this.getOrElseUpdate(target, mutable.Set.empty)
            hosts += host
          }

          okToAdd
        }

        /** whether the first argument is reachable following zero or more links starting at the second argument. */
        def isReachableFrom(fst: MethodNode, snd: MethodNode): Boolean = {
          if(fst == snd) {
            return true
          }
          this.get(snd) match {
            case Some(nodes) => nodes exists { n => isReachableFrom(fst, n) } // there are no cycles, thus this terminates.
            case None        => false
          }
        }

      } // end of object dagset

      for(cgn <- cgns) {
        cgn.hiOs  = cgn.hiOs  filter { it: InlineTarget => dagset.linkUnlessCycle(it.callee, cgn.host) }
        cgn.procs = cgn.procs filter { it: InlineTarget => dagset.linkUnlessCycle(it.callee, cgn.host) }
      }

      /**
       *  It only remains to visit the elements of `cgns` in an order that ensures
       *  a CallGraphNode has stabilitzed (ie all inlinings have been performed inside it, with stable calees)
       *  by the time it's inlined into a host method.
       */
      val remaining = mutable.Set.empty[CallGraphNode]
      remaining ++= cgns.toList
      while(remaining.nonEmpty) {

        val leaves = remaining.filter( cgn => cgn.candidates.forall( c => !mn2cgn.contains(c.callee) || !remaining.contains(mn2cgn(c.callee)) ) )
        assert(leaves.nonEmpty, "Otherwise loop forever")

        leaves foreach { leaf  => inlineCallees(leaf) }

        remaining --= leaves
      }

    } // end of method inlining()

    /**
     *
     */
    private def inlineCallees(leaf: CallGraphNode) {

      // debug: `Util.textify(leaf.host)` can be used to record (before and after) what the host-method looks like.

      //----------------------------------------------------------------------
      // Part 0 of 2: Type-Flow Analysis to determine non-nullness of receiver
      //----------------------------------------------------------------------
      val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
      tfa.analyze(leaf.hostOwner.name, leaf.host)
      // looking up in array `frames` using the whatever-then-current index of `insn` would assume the instruction list hasn't changed.
      // while in general after adding or removing instructions an analysis should be re-run,
      // for the purposes of inlining it's ok to have at hand for a callsite its frame as it was when the analysis was computed.
      val tfaFrameAt: Map[MethodInsnNode, asm.tree.analysis.Frame[TFValue]] = {
        leaf.candidates.map(it => it.callsite -> tfa.frameAt(it.callsite).asInstanceOf[asm.tree.analysis.Frame[TFValue]]).toMap
      }

      //-----------------------------
      // Part 1 of 2: method-inlining
      //-----------------------------
      leaf.procs foreach { proc =>

        inlineMethod(
          leaf.hostOwner.name,
          leaf.host,
          proc.callsite,
          tfaFrameAt(proc.callsite),
          proc.callee
        )

      }
      leaf.procs = Nil

      //------------------------------
      // Part 2 of 2: closure-inlining
      //------------------------------
      leaf.hiOs foreach { hiO =>

        val callsiteTypeFlow: asm.tree.analysis.Frame[TFValue] = tfaFrameAt(hiO.callsite)

        val success = inlineClosures(
          leaf.hostOwner,
          leaf.host,
          hiO.callsite,
          callsiteTypeFlow,
          hiO.callee,
          hiO.owner
        )

        if(success) {
          val hasNonNullReceiver = isReceiverKnownNonNull(callsiteTypeFlow, hiO.callsite)
          logSuccessfulInlining(leaf.hostOwner.name, leaf.host, hiO.callsite, isHiO = true, hasNonNullReceiver)
        }

      }
      leaf.hiOs = Nil

      // debug
      val da = new Analyzer[BasicValue](new asm.tree.analysis.BasicVerifier)
      da.analyze(leaf.hostOwner.name, leaf.host)
    }

    /**
     * SI-5850: Inlined code shouldn't forget null-check on the original receiver
     */
    private def isReceiverKnownNonNull(frame: asm.tree.analysis.Frame[TFValue], callsite: MethodInsnNode): Boolean = {
      callsite.getOpcode match {
        case Opcodes.INVOKEDYNAMIC => false // TODO
        case Opcodes.INVOKESTATIC  => true
        case Opcodes.INVOKEVIRTUAL   |
             Opcodes.INVOKESPECIAL   |
             Opcodes.INVOKEINTERFACE =>
          val rcv:  TFValue = frame.getReceiver(callsite)
          assert(rcv.lca.hasObjectSort)
          rcv.isNonNull
      }
    }

    /**
     * This method takes care of all the little details around inlining the callee's instructions for a callsite located in a `host` method.
     * Those details boil down to:
     *   (a) checking whether inlining is feasible. If unfeasible, don't touch anything and return false.
     *   (b) replacing the callsite with:
     *       STORE instructions for expected arguments,
     *       callee instructions adapted to their new environment
     *         (accesses to local-vars shifted,
     *          RETURNs replaced by jumps to the single-exit of the inlined instructions,
     *          without forgetting to empty all the stack slots except stack-top right before jumping)
     *   (c) copying over the debug info from the callee's
     *   (d) re-computing the maxLocals and maxStack of the host method.
     *   (e) return true.
     *
     * Inlining is considered unfeasible in two cases, summarized below and described in more detail on the spot:
     *   (a.1) due to the possibility of the callee clearing the operand-stack when entering an exception-handler, as well as
     *   (a.2) inlining would lead to illegal access errors.
     *
     * @param hostOwner the internal name of the class declaring the host method
     * @param host      the method containing a callsite for which inlining has been requested
     * @param callsite  the invocation whose inlining is requested.
     * @param frame     informs about stack depth at the callsite
     * @param callee    the actual method-implementation that will be dispatched at runtime.
     *
     * @return true iff method-inlining was actually performed.
     *
     */
    private def inlineMethod(hostOwner: String,
                             host:      MethodNode,
                             callsite:  MethodInsnNode,
                             frame:     asm.tree.analysis.Frame[TFValue],
                             callee:    MethodNode): Boolean = {

      assert(host.instructions.contains(callsite))
      assert(callee != null)
      assert(callsite.name == callee.name)
      assert(callsite.desc == callee.desc)

      /*
       * The first situation (a.1) under which method-inlining is unfeasible: In case both conditions below hold:
       *   (a.1.i ) the operand stack may be cleared in the callee, and
       *   (a.1.ii) the stack at the callsite in host contains more values than args expected by the callee.
       *
       * Alternatively, additional STORE instructions could be inserted to park those extra values while the inlined body executes,
       * but the overhead doesn't make it worth the effort.
       */
      if(!callee.tryCatchBlocks.isEmpty) {
        val stackHeight       = frame.getStackSize
        val expectedArgs: Int = Util.expectedArgs(callsite)
        if(stackHeight > expectedArgs) {
          // TODO warning()
          return false
        }
        assert(stackHeight == expectedArgs)
      }

      // instruction cloning requires the following map to consistently replace new for old LabelNodes.
      val labelMap = Util.clonedLabels(callee)

      /*
       * In general callee.instructions and bodyInsns aren't same size,
       * for example because calleeInsns may contain FrameNodes which weren't cloned into body.
       * Therefore, don't try to match up original and cloned instructions by position!
       * Instead, `insnMap` is a safe way to find a cloned instruction using the original as key.
       */
      val insnMap   = new java.util.HashMap[AbstractInsnNode, AbstractInsnNode]()
      val body      = Util.clonedInsns(callee.instructions, labelMap, insnMap)
      val bodyInsns = body.toArray

      /*
       * In case the callee has been parsed from bytecode,
       * its instructions may refer to type descriptors and internal names
       * that as of yet lack a corresponding TypeName in Names.chrs
       * (the GenBCode infrastructure standardizes on TypeNames for lookups.
       * The utility below takes care of creating TypeNames for those descriptors and internal names.
       * Even if inlining proves unfeasible, those TypeNames won't cause any harm.
       *
       * TODO why weren't those TypeNames entered as part of parsing callee from bytecode?
       *      After all, we might want to run e.g. Type-Flow Analysis on external methods before inlining them.
       */
      codeRepo.enterExemplarsForUnseenTypeNames(body)

      if(!allAccessesLegal(body, lookupRefBType(hostOwner))) {
        // TODO warning()
        return false
      }

      // By now it's a done deal that method-inlining will be performed. There's no going back.

      // each local-var access in `body` is shifted host.maxLocals places
      for(bodyInsn <- bodyInsns; if bodyInsn.getType == AbstractInsnNode.VAR_INSN) {
        val lvi = bodyInsn.asInstanceOf[VarInsnNode]
        lvi.`var` += host.maxLocals
      }

      val calleeMethodType = BType.getMethodType(callee.desc)

      // add a STORE instruction for each expected argument, including for THIS instance if any.
      val argStores   = new InsnList
      var nxtLocalIdx = host.maxLocals
      if(Util.isInstanceMethod(callee)) {
        argStores.insert(new VarInsnNode(Opcodes.ASTORE, nxtLocalIdx))
        nxtLocalIdx    += 1
      }
      for(at <- calleeMethodType.getArgumentTypes) {
        val opc         = at.toASMType.getOpcode(Opcodes.ISTORE)
        argStores.insert(new VarInsnNode(opc, nxtLocalIdx))
        nxtLocalIdx    += at.getSize
      }
      body.insert(argStores)

      // body's last instruction is a LabelNode denoting the single-exit point
      val postCall   = new asm.Label
      val postCallLN = new asm.tree.LabelNode(postCall)
      postCall.info  = postCallLN
      body.add(postCallLN)

          /**
           * body may contain xRETURN instructions, each should be replaced at that program point
           * by DROPs (as needed) for all slots but stack-top.
           */
          def replaceRETURNs() {
            val retType        = calleeMethodType.getReturnType
            val hasReturnValue = !retType.isUnitType
            val retVarIdx      = nxtLocalIdx
            nxtLocalIdx       += retType.getSize

            if(hasReturnValue) {
              val retVarLoad = {
                val opc = retType.toASMType.getOpcode(Opcodes.ILOAD)
                new VarInsnNode(opc, retVarIdx)
              }
              assert(body.getLast == postCallLN)
              body.insert(body.getLast, retVarLoad)
            }

                def retVarStore(retInsn: InsnNode) = {
                  val opc = retInsn.getOpcode match {
                    case Opcodes.IRETURN => Opcodes.ISTORE
                    case Opcodes.LRETURN => Opcodes.LSTORE
                    case Opcodes.FRETURN => Opcodes.FSTORE
                    case Opcodes.DRETURN => Opcodes.DSTORE
                    case Opcodes.ARETURN => Opcodes.ASTORE
                  }
                  new VarInsnNode(opc, retVarIdx)
                }

            val ca = new Analyzer[BasicValue](new BasicInterpreter)
            ca.analyze(callsite.owner, callee)
            val insnArr = callee.instructions.toArray // iterate this array while mutating callee.instructions at will
            for(calleeInsn <- insnArr;
                if calleeInsn.getOpcode >= Opcodes.IRETURN && calleeInsn.getOpcode <= Opcodes.RETURN)
            {
              val retInsn = calleeInsn.asInstanceOf[InsnNode]
              val frame   = ca.frameAt(retInsn)
              val height  = frame.getStackSize
              val counterpart = insnMap.get(retInsn)
              assert(counterpart.getOpcode == retInsn.getOpcode)
              assert(hasReturnValue == (retInsn.getOpcode != Opcodes.RETURN))
              val retRepl = new InsnList
              // deal with stack-top: either drop it or keep its value in retVar
              if(hasReturnValue)  { retRepl.add(retVarStore(retInsn)) }
              else if(height > 0) { retRepl.add(Util.getDrop(frame.peekDown(0).getSize)) }
              // deal with the rest of the stack
              for(slot <- 1 until height) {
                retRepl.add(Util.getDrop(frame.peekDown(slot).getSize))
              }
              retRepl.add(new JumpInsnNode(Opcodes.GOTO, postCallLN))
              body.insert(counterpart, retRepl)
              body.remove(counterpart)
            }
          }

      replaceRETURNs()

      host.instructions.insert(callsite, body) // after this point, body.isEmpty (an ASM instruction can be owned by a single InsnList)
      host.instructions.remove(callsite)

      // let the host know about the debug info of the callee
      host.localVariables.addAll(Util.cloneLocalVariableNodes(callee, labelMap, callee.name + "_"))
      host.tryCatchBlocks.addAll(Util.cloneTryCatchBlockNodes(callee, labelMap))

      // the host's local-var space grows by the local-var space of the callee, plus another local-var in case hasReturnValue
      Util.computeMaxLocalsMaxStack(host)
      assert(host.maxLocals >= nxtLocalIdx) // TODO why not == ?

      logSuccessfulInlining(hostOwner, host, callsite, isHiO = false, isReceiverKnownNonNull(frame, callsite))

      true

    } // end of method inlineMethod()

    def logSuccessfulInlining(hostOwner: String,
                              host:      MethodNode,
                              callsite:  MethodInsnNode,
                              isHiO:     Boolean,
                              isReceiverKnownNonNull: Boolean) {
      val remark =
        if(isReceiverKnownNonNull) ""
        else " (albeit null receiver couldn't be ruled out)"

      val kind = if(isHiO) "closure-inlining" else "method-inlining"

      log("Successful " + kind + remark +
          ". Callsite: " + callsite.owner + "." + callsite.name + callsite.desc +
          " , occurring in method " + hostOwner + "::" + host.name + "." + host.desc)
    }

    /**
     * The second situation (a.2) under which method-inlining is unfeasible:
     *   In case access control doesn't give green light.
     *   Otherwise a java.lang.IllegalAccessError would be thrown at runtime.
     *
     * Quoting from the JVMS (our terminology: `there` stands for `C`; `here` for `D`):
     *
     *  5.4.4 Access Control
     *
     *  A class or interface C is accessible to a class or interface D if and only if either of the following conditions is true:
     *    (cond A1) C is public.
     *    (cond A2) C and D are members of the same runtime package (Sec 5.3).
     *
     *  A field or method R is accessible to a class or interface D if and only if any of the following conditions are true:
     *    (cond B1) R is public.
     *    (cond B2) R is protected and is declared in a class C, and D is either a subclass of C or C itself.
     *              Furthermore, if R is not static, then the symbolic reference to R
     *              must contain a symbolic reference to a class T, such that T is either a subclass
     *              of D, a superclass of D or D itself.
     *    (cond B3) R is either protected or has default access (that is, neither public nor
     *              protected nor private), and is declared by a class in the same runtime package as D.
     *    (cond B4) R is private and is declared in D.
     *
     *  This discussion of access control omits a related restriction on the target of a
     *  protected field access or method invocation (the target must be of class D or a
     *  subtype of D). That requirement is checked as part of the verification process
     *  (Sec 5.4.1); it is not part of link-time access control.
     *
     *  @param body
     *              instructions that will be inlined in a method in class `here`
     *  @param here
     *              class from which accesses given by `body` will take place.
     *
     */
    private def allAccessesLegal(body: InsnList, here: BType): Boolean = {

          def isAccessible(there: BType): Boolean = {
            if(!there.isNonSpecial) true
            else if (there.isArray) isAccessible(there.getElementType)
            else {
              assert(there.hasObjectSort, "not of object sort: " + there.getDescriptor)
              (there.getRuntimePackage == here.getRuntimePackage) || exemplars.get(there).isPublic
            }
          }

          /**
           * @return whether the first argument is a subtype of the second, or both are the same BType.
           */
          def isSubtypeOrSame(a: BType, b: BType): Boolean = {
            (a == b) || {
              val ax = exemplars.get(a)
              val bx = exemplars.get(b)

              (ax != null) && (bx != null) && ax.isSubtypeOf(b)
            }
          }

          /**
           * Furthermore, if R is not static, then the symbolic reference to R
           * must contain a symbolic reference to a class T, such that T is either a subclass
           * of D, a superclass of D or D itself.
           */
          def sameLineage(thereSymRef: BType): Boolean = {
            (thereSymRef == here) ||
            isSubtypeOrSame(thereSymRef, here) ||
            isSubtypeOrSame(here, thereSymRef)
          }

          def samePackageAsHere(there: BType): Boolean = { there.getRuntimePackage == here.getRuntimePackage }

          def memberAccess(flags: Int, thereOwner: BType, thereSymRef: BType) = {
            val key = { (Opcodes.ACC_PUBLIC | Opcodes.ACC_PROTECTED | Opcodes.ACC_PRIVATE) & flags }
            key match {

              case 0 /* default access */ => // (cond B3)
                samePackageAsHere(thereOwner)

              case Opcodes.ACC_PUBLIC     => // (cond B1)
                true

              case Opcodes.ACC_PROTECTED  =>
                // (cond B2)
                val condB2 = isSubtypeOrSame(here, thereOwner) && {
                  val isStatic = ((Opcodes.ACC_STATIC & flags) != 0)
                  isStatic || sameLineage(thereSymRef)
                }
                condB2 || samePackageAsHere(thereOwner)

              case Opcodes.ACC_PRIVATE    => // (cond B4)
                (thereOwner == here)
            }
          }

      val iter = body.iterator()
      while(iter.hasNext) {
        val insn    = iter.next()
        val isLegal = insn match {

          case ti: TypeInsnNode  => isAccessible(lookupRefBType(ti.desc))

          case fi: FieldInsnNode =>
            val fowner: BType = lookupRefBType(fi.owner)
            val fn: FieldNode = codeRepo.getFieldOrNull(fowner, fi.name, fi.desc)
            (fn != null) && memberAccess(fn.access, fowner, fowner)

          case mi: MethodInsnNode =>
            val thereSymRef: BType  = lookupRefBType(mi.owner)
            val mnAndOwner = codeRepo.getMethodOrNull(thereSymRef, mi.name, mi.desc) // TODO look up in superclasses too
            (mnAndOwner != null) && {
              val MethodNodeAndOwner(mn, thereClassNode) = mnAndOwner
              val thereOwner = lookupRefBType(thereClassNode.name)
              memberAccess(mn.access, thereOwner, thereSymRef)
            }

          case ivd: InvokeDynamicInsnNode => false // TODO

          case ci: LdcInsnNode =>
            ci.cst match {
              case t: asm.Type => isAccessible(lookupRefBType(t.getInternalName))
              case _           => true
            }

          case ma: MultiANewArrayInsnNode =>
            val et = descrToBType(ma.desc).getElementType
            if(et.hasObjectSort) isAccessible(et)
            else true

          case _ => true
        }
        if(!isLegal) {
          return false
        }
      }

      true
    } // end of method allAccessesLegal()

    /**
     * This method inlines the invocation of a "higher-order method" and
     * stack-allocates the anonymous closures received as arguments.
     *
     * "Stack-allocating" in the sense of "scalar replacement of aggregates" (see also "object fusion").
     * This can always be done for closures converted in UnCurry via `closureConversionMethodHandle()`
     * a conversion that has the added benefit of minimizing pointer-chasing (heap navigation).
     *
     *
     * Rationale
     * ---------
     *
     * Closure inlining results in faster code by specializing a higher-order method
     * to the particular anonymous closures given as arguments at a particular callsite
     * (at the cost of code duplication, namely of the Hi-O method, no other code gets duplicated).
     *
     * The "Hi-O" method usually applies the closure inside a loop (e.g., map and filter fit this description)
     * that's why a hi-O callsite can be regarded for most practical purposes as a loop-header.
     * "Regarded as a loop header" because we'd like the JIT to pick that code section for compilation.
     * If actually a loop-header, and the instructions for the hi-O method were inlined,
     * then upon OnStackReplacement the whole method containing the hi-O invocation would have to be compiled
     * (which might well not be hot code itself).
     *
     * To minimize that wasted effort, `inlineClosures()` creates a dedicated (static, synthetic) method
     * for a given combination of hi-O and closures to inline
     * (not all closures might be amenable to inlining, details below).
     * In that method, closure-apply() invocations are inlined, thus cancelling out:
     *   - any redundant box-unbox pairs when passing arguments to closure-apply(); as well as
     *   - any unbox-box pair for its return value.
     *
     *
     * Terminology
     * -----------
     *
     * hi-O method:     the "higher-order" method taking one or more closure instances as argument. For example, Range.foreach()
     *
     * closure-state:   the values of fields of an anonymous-closure-class, all of them final.
     *                  In particular an $outer field is present whenever the closure "contains" inner classes (in particular, closures).
     *
     * closure-methods: apply() which possibly forwards to a specialized variant after unboxing some of its arguments.
     *                  For a closure converted in UnCurry:
     *                    - via `closureConversionMethodHandle()` there are no additional closure-methods.
     *                    - via `closureConversionTraditional()`  those methods that were local to the source-level apply()
     *                      also become closure-methods after lambdalift.
     *
     * closure-constructor: a sequence of assignments to initialize the (from then on immutable) closure-state by copying arguments' values.
     *                      The first such argument is always the THIS of the invoker,
     *                      which becomes the $outer value from the perspective of the closure-class.
     *
     *
     * Closure lifecycle
     * -----------------
     *
     * In terms of bytecode, two code sections are relevant: instantiation of AC (the "Anonymous Closure") and passing it as argument to Hi-O:
     *
     *     NEW AC
     *     DUP
     *     // load of closure-state args, the first of which is THIS
     *     INVOKESPECIAL < init >
     *
     * The above in turn prepares the i-th argument as part of this code section:
     *
     *     // instructions that load (i-1) args
     *     // here goes the snippet above (whose instructions load the closure instance we want to elide)
     *     // more args get loaded
     *     INVOKE Hi-O
     *
     * In order to stack-allocate a particular closure passed to Hi-O, the closure in question shouldn't escape from Hi-O.
     * There's in fact a whole cascade of prerequisites to check,
     * desribed in detail in the helper methods used for that purpose (see method body).
     *
     * TODO documentation about the bytecode-rewriting.
     *
     * @param hostOwner the class declaring the host method
     * @param host      the method containing a callsite for which inlining has been requested
     * @param callsite  invocation of a higher-order method (taking one or more closures) whose inlining is requested.
     * @param callsiteTypeFlow the type-stack reaching the callsite. Useful for knowing which args are closure-typed.
     * @param hiO       the actual implementation of the higher-order method that will be dispatched at runtime
     * @param hiOOwner  the Classnode where callee was declared.
     *
     * @return true iff inlining was actually performed.
     *
     */
    private def inlineClosures(hostOwner: ClassNode,
                               host:      MethodNode,
                               callsite:  MethodInsnNode,
                               callsiteTypeFlow: asm.tree.analysis.Frame[TFValue],
                               hiO:       MethodNode,
                               hiOOwner:  ClassNode): Boolean = {

      // val txtHost = Util.textify(host) // debug
      // val txtHiO  = Util.textify(hiO)  // debug

      codeRepo.enterExemplarsForUnseenTypeNames(hiO.instructions)

      if(!allAccessesLegal(hiO.instructions, lookupRefBType(hostOwner.name))) {
        // TODO warning()
        return false
      }

            /**
             *  Which params of the hiO method receive closure-typed arguments?
             *
             *  Param-positions are zero-based.
             *  The receiver (of an instance method) is ignored: "params" refers to those listed in a JVM-level method descriptor.
             *  There's a difference between formal-param-positions (as returned by this method) and local-var-indexes (as used in a moment).
             *  The latter take into account the JVM-type-size of previous locals, while param-positions are numbered consecutively.
             *
             *  @return the positions of those hiO method-params taking a closure-typed actual argument.
             */
            def survivors1(): collection.Set[Int] = {

              val actualsTypeFlow: Array[TFValue] = callsiteTypeFlow.getActualArguments(callsite) map (_.asInstanceOf[TFValue])
              var idx = 0
              var survivors = mutable.LinkedHashSet[Int]()
              while(idx < actualsTypeFlow.length) {
                val tf = actualsTypeFlow(idx)
                if(tf.lca.isClosureClass) {
                  survivors += idx
                }
                idx += 1
              }

              survivors
            }

      val closureTypedHiOArgs = survivors1()
      if(closureTypedHiOArgs.isEmpty) {
        // TODO inlineMethod. Example, `global.log` in `def log(msg: => AnyRef) { global.log(msg) }` will have empty closureTypedArgs
        return false
      }

          /**
           * Pre-requisites on host method
           *
           * Given
           *   (1) a copy-propagating, params-aware, Consumers-Producers analysis of the host method,
           *   (2) the previous subset of params (ie those receiving closure-typed actual arguments)
           * determine those params that receive a unique closure, and look up the ClassNode for the closures in question.
           *
           * N.B.: Assuming the standard compiler transforms as of this writing, `survivors2()` isn't strictly necessary.
           * However it protects against any non-standard transforms that mess up with preconds required for correctness.
           *
           * `survivors2()` goes over the formals in `survivors1()`, picking those that have a single producer,
           * such that the value thus produced is the only actual for the formal in question.
           *
           * Given that the type of the actual fulfills Tracked.isClosureClass,
           * the ClassNode of that type can be found in codeRepo.classes (ie it's being compiled in this run).
           *
           * @return a map with an entry for each hiO method-param that takes a closure,
           *         where an entry maps the position of the method-param to a closure class.
           */
          def survivors2(): Map[Int, ClassNode] = {

            // TODO if cpHost where to be hoisted out of this method, cache `cpHost.frameAt()` before hiOs are inlined.
            val cpHost: UnBoxAnalyzer = UnBoxAnalyzer.create()
            cpHost.analyze(hostOwner.name, host)
            val callsiteCP: asm.tree.analysis.Frame[SourceValue] = cpHost.frameAt(callsite)
            val actualsProducers: Array[SourceValue] = callsiteCP.getActualArguments(callsite) map (_.asInstanceOf[SourceValue])
            val closureProducers: Map[SourceValue, Int] = closureTypedHiOArgs.map(idx => (actualsProducers(idx) -> idx)).toMap

            for(
              (prods, idx) <- closureProducers;
              if (prods.insns.size() == 1);
              singleProducer = prods.insns.iterator().next();
              if(singleProducer.getOpcode == Opcodes.NEW);
              closureBT = lookupRefBType(singleProducer.asInstanceOf[TypeInsnNode].desc)
              if(!isPartialFunctionType(closureBT))
            ) yield (idx, codeRepo.classes.get(closureBT))
          }

      val closureClassPerHiOFormal = survivors2()
      if(closureClassPerHiOFormal.isEmpty) {
        // TODO warn.
        return false
      }

          /**
           * Pre-requisites on hiO method
           *
           * A closure `f` used in hiO method can be stack-allocated provided
           * all usages are of the form `f.apply(...)`, and only of that form.
           *
           * This is checked bytecode-level by looking up all usages of hiO's method-param conveying `f`
           * and checking whether they're of the form shown above.
           *
           * @return for each closure-conveying param in method hiO,
           *         information about that closure and its usages (see `ClosureUsages`).
           *
           */
          def survivors3(): Iterable[ClosureUsages] = {

            val cpHiO: ProdConsAnalyzer = ProdConsAnalyzer.create()
            cpHiO.analyze(hiOOwner.name, hiO)

            val mtHiO = BType.getMethodType(hiO.desc)
            val isInstanceMethod = Util.isInstanceMethod(hiO)

                /**
                 *  Checks whether all closure-usages (in hiO) are of the form `closure.apply(...)`
                 *  and if so return the MethodNode for that apply(), null otherwise.
                 *
                 *  @param closureClass     class realizing the closure of interest
                 *  @param localVarIdxHiO   local-var in hiO (a formal param) whose value is the closure of interest
                 *  @param closureArgUsages instructions where the closure is used as input
                 */
                def areAllApplyCalls(closureClass: ClassNode, localVarIdxHiO: Int, closureArgUsages: collection.Set[AbstractInsnNode]): MethodNode = {

                  // (1) all usages are invocations
                  if(closureArgUsages.exists(insn => insn.getType != AbstractInsnNode.METHOD_INSN)) {
                    return null // TODO warn
                  }

                  // (2) moreover invocations of one and the same method
                  var iter: Iterator[AbstractInsnNode] = closureArgUsages.iterator
                  val fst = iter.next().asInstanceOf[MethodInsnNode]
                  while(iter.hasNext) {
                    val nxt = iter.next().asInstanceOf[MethodInsnNode]
                    if(
                      fst.getOpcode != nxt.getOpcode ||
                      fst.owner     != nxt.owner     ||
                      fst.name      != nxt.name      ||
                      fst.desc      != nxt.desc
                    ) {
                      return null // TODO warn
                    }
                  }

                  // (3) each invocation takes the closure instance as receiver, and only as receiver (ie not as argument)
                  iter = closureArgUsages.iterator
                  while(iter.hasNext) {

                        def isClosureLoad(sv: SourceValue) = {
                          (sv.insns.size() == 1) && {
                            sv.insns.iterator().next() match {
                              case lv: VarInsnNode => lv.`var` == localVarIdxHiO
                              case _ => false
                            }
                          }
                        }

                    val nxt = iter.next().asInstanceOf[MethodInsnNode]
                    val frame = cpHiO.frameAt(nxt)
                    val isDispatchedOnClosure = isClosureLoad(frame.getReceiver(nxt))
                    val passesClosureAsArgument = {
                      frame.getActualArguments(nxt).exists(v => isClosureLoad(v.asInstanceOf[SourceValue]))
                    }

                    if(!isDispatchedOnClosure || passesClosureAsArgument) {
                      return null // TODO warn
                    }
                  }

                  // (4) whether it's actually an apply or specialized-apply invocation
                  val arity = BType.getMethodType(fst.desc).getArgumentCount
                  if(arity > definitions.MaxFunctionArity) {
                    return null // TODO warn
                  }

                  // all checks passed, look up applyMethod
                  val closureClassBType = lookupRefBType(closureClass.name)
                  val tentative = codeRepo.getMethodOrNull(closureClassBType, fst.name, fst.desc)
                  val applyMethod =
                    if(tentative == null) { null }
                    else { tentative.mnode }

                  applyMethod
                }

            for (
              (formalParamPosHiO, closureClass) <- closureClassPerHiOFormal;
              localVarIdxHiO = mtHiO.convertFormalParamPosToLocalVarIdx(formalParamPosHiO, isInstanceMethod);
              closureArgUsages: Set[AbstractInsnNode] = JSetWrapper(cpHiO.consumersOfLocalVar(localVarIdxHiO)).toSet;
              applyMethod = areAllApplyCalls(closureClass, localVarIdxHiO, closureArgUsages);
              if applyMethod != null
            ) yield ClosureUsages(
              formalParamPosHiO,
              localVarIdxHiO,
              closureClass,
              applyMethod,
              closureArgUsages map (_.asInstanceOf[MethodInsnNode])
            )
          }

      val closureClassUtils =
        for (
          cu <- survivors3().toArray;
          ccu = ClosureClassUtil(cu);
          if ccu.isRepOK
        ) yield ccu

      if(closureClassUtils.isEmpty) {
        // TODO warn.
        return false
      }

      val shio = StaticHiOUtil(hiO, closureClassUtils)
      val staticHiO: MethodNode = shio.buildStaticHiO(hiOOwner, callsite)
      val wasInlined = shio.rewriteHost(hostOwner, host, callsite, staticHiO)
      if(wasInlined) {
        // TODO hostOwner.methods.add(staticHiO)
      }

      false
    }

    /**
     *  For a given pair (hiO method, closure-argument) an instance of ClosureUsages
     *  records the apply() invocations for that closure-argument.
     *
     *  @param formalParamPosHiO zero-based position in the formal-params-list of hiO method
     *  @param localVarIdxHiO    corresponding index into the locals-array of hiO method
     *                           (in general different from formalParamPosHiO due to JVM-type-sizes)
     *  @param closureClass
     *  @param applyMethod
     *  @param usages
     */
    case class ClosureUsages(
      formalParamPosHiO: Int,
      localVarIdxHiO:    Int,
      closureClass:      ClassNode,
      applyMethod:       MethodNode,
      usages:            Set[MethodInsnNode]
    )

    /**
     *  Query methods that dig out information hidden in the structure of a closure-class.
     */
    case class ClosureClassUtil(closureUsages: ClosureUsages) {

      def closureClass: ClassNode = closureUsages.closureClass

      val constructor: MethodNode = {
        var result: MethodNode = null
        val iter = closureClass.methods.iterator()
        while(iter.hasNext) {
          val nxt = iter.next()
          if(nxt.name == "<init>") {
            assert(result == null, "duplicate <init> method found in closure-class: " + closureClass.name)
            result = nxt
          }
        }
        Util.computeMaxLocalsMaxStack(result)

        result
      }

      val constructorMethodType = BType.getMethodType(constructor.desc)

      /**
       *  The constructor of a closure-class has params for (a) the outer-instance; and (b) captured-locals.
       *  Those values are stored in final-fields of the closure-class (the so called "closure state")
       *  to serve later as actual arguments in a "delegate-invoking apply()".
       *
       *  From the perspective of `host` (which invokes `hiO`) the closure-state aliases the actuals
       *  to the closure instantiation. When the time comes to inline that apply
       *  (containing usages of closure-state fields) their correspondence with the values they alias is needed because:
       *    (a) `host` knowns only what actuals go to which closure-constructor-param-positions; and
       *    (b) there's no guarantee that those values appear in the same order in both
       *        - closure instantiation, and
       *        - delegate-invoking apply invocation.
       *
       *  This map tracks the aliasing of closure-state values, before and after the closure was instantiated.
       */
      val stateField2constrParam: Map[String, Int] = {

        val cpConstructor: ProdConsAnalyzer = ProdConsAnalyzer.create()
        cpConstructor.analyze(closureClass.name, constructor)

        /*
         * for each constructor-param-position:
         *   obtain its local-var index
         *   find the single consumer of a LOAD of that local-var (should be a PUTFIELD)
         *   add pair to map.
         **/
        val constructorBT = BType.getMethodType(constructor.desc)

            def findClosureStateField(localVarIdx: Int): String = {
              val consumers = cpConstructor.consumersOfLocalVar(localVarIdx)
              if(localVarIdx == 1) {
                // for outer-param, don't count IFNULL instruction as consumer
                val consumerIter = consumers.iterator()
                var stop = false
                while(consumerIter.hasNext && !stop) {
                  val cnext = consumerIter.next
                  if(cnext.getOpcode == Opcodes.IFNULL) {
                    consumers.remove(cnext)
                    stop = true
                  }
                }
              }
              val consumer: AbstractInsnNode = cpConstructor.getSingleton(consumers)
              consumer match {
                case null => null
                case fi: FieldInsnNode
                  if (fi.getOpcode == Opcodes.PUTFIELD ) &&
                     (fi.owner     == closureClass.name)
                          => fi.name
                case _    => null
              }
            }

        val result =
          for(
            paramPos <- 0 until constructorBT.getArgumentCount;
            localVarIdx = constructorBT.convertFormalParamPosToLocalVarIdx(paramPos, isInstanceMethod = true);
            fieldName   = findClosureStateField(localVarIdx);
            if fieldName != null
          ) yield (fieldName -> paramPos)

        result.toMap
      }

      private def getClosureState(fieldName: String): FieldNode = {
        val fIter = closureClass.fields.iterator()
        while(fIter.hasNext) {
          val f = fIter.next()
          if(Util.isInstanceField(f) && (f.name == fieldName)) {
            return f
          }
        }

        null
      }

      val field: Map[String, FieldNode] = {
        val result =
          for(
            (fieldName, _) <- stateField2constrParam;
            fn = getClosureState(fieldName);
            if fn != null
          ) yield (fieldName -> fn)

        result.toMap
      }

      def isRepOK: Boolean = {
        /*
         * number of closure-state fields should be one less than number of fields in closure-class
         * (static field SerialVersionUID isn't part of closure-state).
         */
        (stateField2constrParam.size == (closureClass.fields.size() - 1)) &&
        (stateField2constrParam.size == field.size)

        // TODO all apply methods have been accounted for, there are no additional methods

      }

      /**
       *  A "delegate-invoking apply()" is the apply method
       *  (of a closureClass converted by `closureConversionMethodHandle()`)
       *  in charge of invoking the hoisted method that encapsulates the original closure body.
       *
       *  Example:
       *        < specialized > def apply$mcVI$sp(v1: Int): Unit = $outer.C$$dlgt1$1(v1);
       */
      def isDelegateInvokingApply(mnode: MethodNode): Boolean = {
        false // TODO
      }

      /**
       *  Example 1 of "forwarding apply()"
       *
       *        final def apply(x$1: Int): Unit = apply$mcVI$sp(x$1);
       *
       *  Example 2 of "forwarding apply()"
       *
       *        final < bridge > < artifact > def apply(v1: Object): Object = {
       *          apply(scala.Int.unbox(v1));
       *          scala.runtime.BoxedUnit.UNIT
       *        };
       *
       */
      def isForwardingApply(mnode: MethodNode): Boolean = {
        false // TODO
      }

    } // end of class ClosureClassUtil

    /**
     *  Query methods that help derive a "static hiO method" given a "hiO method".
     */
    case class StaticHiOUtil(hiO: MethodNode, closureClassUtils: Array[ClosureClassUtil]) {

      val howMany = closureClassUtils.size

      /**
       *  Which (zero-based) param-positions in hiO correspond to closures to be inlined.
       */
      val isInlinedParamPos: Set[Int] = {
        closureClassUtils.map( ccu => ccu.closureUsages.formalParamPosHiO ).toSet
      }

      /**
       *  Form param-positions in hiO corresponding to closures to be inlined, their local-variable index.
       */
      val isInlinedLocalIdx: Set[Int] = {
        closureClassUtils.map( ccu => ccu.closureUsages.localVarIdxHiO).toSet
      }

      /**
       *  The "slack of a closure-receiving method-param of hiO" has to do with the rewriting
       *  by which a staticHiO method is derived from a hiO method.
       *
       *  As part of that rewriting, those params receiving closures that are to be stack-allocated
       *  are replaced with params that receive the closure's state values.
       *  Usages of locals in the rewritten method will in general require shifting.
       *
       *  As a first step, the following map informs for each closure-receiving-param
       *  the accumulated sizes of closure-state params added so far (including those for that closure), minus 1
       *  (accounting for the fact the closure-param will be elided along with the closure-instance).
       *
       *  In the map, an entry has the form:
       *    (original-local-var-idx -> accumulated-sizes-inluding-constructorParams-for-this-closure)
       */
      val closureParamSlack: Array[Tuple2[Int, Int]] = {
        var acc = 0
        val result =
          for(cu <- closureClassUtils)
          yield {
            val constrParams: Array[BType] = cu.constructorMethodType.getArgumentTypes
            constrParams foreach { constrParamBT => acc += constrParamBT.getSize }
            acc -= 1
            // assert(acc >= -1). In other words, not every closure-constructor has at least an outer instance param.

            (cu.closureUsages.localVarIdxHiO -> acc)
          }

        result.sortBy(_._1)
      }

      /**
       *  Not applicable to closure-receiving params themselves (they simply go away), but to all others.
       */
      def shiftedLocalIdx(original: Int): Int = {
        val accOpt = closureParamSlack.find(_._1 >= original)
        if(accOpt.isEmpty) original
        else {
          val Pair(paramIdx, acc) = accOpt.get
          assert(paramIdx != original)
          original + acc
        }
      }

      def buildStaticHiO(hostOwner: ClassNode, callsite: MethodInsnNode): MethodNode = {

        // (1) method name
        val name = {
          var attempt = 1
          var candidate: String = null
          var duplicate = false
          do {
            candidate = "shio$" + attempt + "$" + hiO.name
            duplicate = JListWrapper(hostOwner.methods) exists { mn => mn.name == candidate }
            attempt += 1
          } while(duplicate)

          candidate
        }

        // (2) method descriptor, computing initial value of staticHiO's maxLocals (will be updated again once stubs are pasted)
        var formals: List[BType] = Nil
        if(Util.isInstanceMethod(hiO)) {
          formals ::= lookupRefBType(callsite.owner)
        }
        val hiOMethodType = BType.getMethodType(hiO.desc)
        var maxLocals = hiO.maxLocals
        foreachWithIndex(hiOMethodType.getArgumentTypes.toList) {
          (hiOParamType, hiOParamPos) =>
            if(isInlinedParamPos(hiOParamPos)) {
              // splice-in the closure's constructor's params, the original closure-receiving param goes away.
              maxLocals -= 1
              val ccu = closureClassUtils.find(_.closureUsages.formalParamPosHiO == hiOParamPos).get
              for(constrParamType <- ccu.constructorMethodType.getArgumentTypes) {
                formals ::= constrParamType
                maxLocals += constrParamType.getSize
              }
            } else {
              formals ::= hiOParamType
            }
        }

        // (3) clone InsnList, get Label map
        val labelMap = Util.clonedLabels(hiO)
        val insnMap  = new java.util.HashMap[AbstractInsnNode, AbstractInsnNode]()
        val body     = Util.clonedInsns(hiO.instructions, labelMap, insnMap)

        // (4) Util.clone TryCatchNodes
        val tcns: java.util.List[TryCatchBlockNode] = Util.cloneTryCatchBlockNodes(hiO, labelMap)

        // (5) Util.clone LocalVarNodes, shift as per-oracle
        val lvns: java.util.List[LocalVariableNode] = Util.cloneLocalVariableNodes(hiO, labelMap, "")
        val lvnIter = lvns.iterator()
        while(lvnIter.hasNext) {
          val lvn: LocalVariableNode = lvnIter.next()
          if(isInlinedLocalIdx(lvn.index)) {
            lvnIter.remove()
          } else {
            lvn.index = shiftedLocalIdx(lvn.index)
          }
        }

        // (6) put together the pieces above into a MethodNode

        // (7) Shift LOADs and STOREs: (a) remove all isInlined LOADs; (b) shift as per oracle
        //     (There are no usages of spliced-in params yet)
        val bodyIter = body.iterator()
        while(bodyIter.hasNext) {
          val insn = bodyIter.next
          if(insn.getType == AbstractInsnNode.VAR_INSN) {
            val vi = insn.asInstanceOf[VarInsnNode]
            assert(vi.getOpcode != Opcodes.RET)
            if(isInlinedLocalIdx(vi.`var`)) {
              bodyIter.remove()
            } else {
              vi.`var` = shiftedLocalIdx(vi.`var`)
            }
          }
        }

        // (8) rewrite usages (closure-apply invocations)
        //     For each usage obtain the stub (it's the same stub for all usages of the same closure), clone and paste.

        // (9) update maxStack, run TFA for debug purposes

        null // TODO
      }

      /**
       * `host` is patched to:
       *   (1) convey closure-constructor-args instead of an instantiated closure; and
       *   (2) target `staticHiO` rather than `hiO`
       *
       * The first step above amounts to removing NEW, DUP, and < init > instructions for closure instantiations.
       *
       * @param hostOwner the class declaring the host method
       * @param host      the method containing a callsite for which inlining has been requested
       * @param callsite  invocation of a higher-order method (taking one or more closures) whose inlining is requested
       * @param staticHiO a static method added to hostOwner, specializes hiO by inlining the closures hiO used to be invoked with
       *
       * @return whether closure-inlining was actually performed (should always be the case unless wrong input bytecode).
       */
      def rewriteHost(hostOwner: ClassNode, host: MethodNode, callsite: MethodInsnNode, staticHiO: MethodNode): Boolean = {

        val cpHost = ProdConsAnalyzer.create()
        cpHost.analyze(hostOwner.name, host)
        val callsiteCP: asm.tree.analysis.Frame[SourceValue] = cpHost.frameAt(callsite)
        val actualsProducers: Array[SourceValue] = callsiteCP.getActualArguments(callsite) map (_.asInstanceOf[SourceValue])

        val newInsns: Array[AbstractInsnNode] =
          for(
            ccu <- closureClassUtils;
            closureParamPos = ccu.closureUsages.formalParamPosHiO;
            newInsnSV       = actualsProducers(closureParamPos)
          ) yield {
            assert(newInsnSV.insns.size() == 1)
            newInsnSV.insns.iterator().next()
          }

        val dupInsns: Array[InsnNode] =
          for(newInsn <- newInsns)
          yield {
            val newConsumers = (JSetWrapper(cpHost.consumers(newInsn)) filter (_ ne callsite))
            assert(newConsumers.size == 1)
            val dupInsn = newConsumers.iterator.next().asInstanceOf[InsnNode]
            assert(dupInsn.getOpcode == Opcodes.DUP)

            dupInsn
          }

        val initInsns: Array[MethodInsnNode] =
          for(dupInsn <- dupInsns)
          yield {
            val initInsn = cpHost.consumers(dupInsn).iterator.next().asInstanceOf[MethodInsnNode]
            assert(initInsn.getOpcode == Opcodes.INVOKESPECIAL && initInsn.name  == "<init>")

            initInsn
          }

        if ((newInsns.length != howMany) || (dupInsns.length != howMany) || (initInsns.length != howMany)) {
          // TODO warn
          return false
        }

        // TODO remove the instructions above

        // val rewiredInvocation = new MethodInsnNode(Opcodes.INVOKESTATIC, hostOwner.name, staticHiO.name, staticHiO.desc)
        // TODO host.instructions.set(callsite, rewiredInvocation)

        true
      } // end of method rewriteHost()

    } // end of class StaticHiOUtil

  } // end of class WholeProgramAnalysis

  /**
   * @param mnode a MethodNode, usually found via codeRepo.getMethod(bt: BType, name: String, desc: String)
   * @param owner ClassNode declaring mnode
   */
  case class MethodNodeAndOwner(mnode: MethodNode, owner: ClassNode) {
    assert(owner.methods.contains(mnode))
  }

} // end of class BCodeOptInter


/*
 * TODO After method-inlining, some IntRef, VolatileIntRef, etc. may not escape anymore and can be converted back to local-vars.
 *
 *  In particular after inlining:
 *    (a) what used to be local-method; or
 *    (b) the delegate invoked by a closure converted via "closureConversionMethodHandle()"
 *
 *  In addition to not escaping, there should be no doubt as to what Ref value is being manipulated
 *  (e.g., merging two Refs prevents from "un-wrapping" it). This can be checked
 *  with a copy-propagating, param-aware, consumers-producers analysis, as follows.
 *  First, find all Ref instantiations, and for each:
 *    (1) check all consumers form a DEMUX,
 *        where each consumer instruction is either a GETFIELD or PUTFIELD of the "elem" field.
 *  Transformation proper:
 *    (2) for each survivor,
 *        (2.a) NEW, DUP, < init > becomes STORE
 *        (2.b) getter: LOAD ref, GETFIELD elem ----> LOAD  var
 *        (2.b) setter: LOAD ref, PUTFIELD elem ----> STORE var
 *  Shifting of local-vars:
 *    A local-var holding a ref holds a category-1 value. After "unwrapping" L or D the local-var will hold a category-2 value.
 *
 **/