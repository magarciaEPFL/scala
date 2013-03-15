/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.UnBoxAnalyzer.FakeParamLoad
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
    elidedClasses.clear()
    closuRepo.clear()
  }

  //--------------------------------------------------------
  // Optimization pack: Method-inlining and Closure-inlining
  //--------------------------------------------------------

  /**
   * During `GenBCode`, `PlainClassBuilder` inspects each MethodNode for a plain class,
   * detecting those callsites targeting @inline methods, and collecting them (the callsites) in a `CallGraphNode` instance,
   * classified into "higher-order callsites" (ie taking one or more functions as arguments) and the rest.
   * The callsites in question constitute "requests for inlining".
   *
   * During `WholeProgramAnalysis.inlining()` An attempt will be made to fulfill the inlining requests,
   * after detecting any attempts at cyclic inlining. Moreover a request may prove unfeasible afterwards too,
   * e.g. due to the callsite program point having a deeper operand-stack than the arguments the callee expects,
   * and the callee containing exception handlers.
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

    def directCallees: Set[MethodNode] = {
      hiOs.map(_.callee).toSet ++ procs.map(_.callee)
    }

    /**
     * Initially the invocation instructions (one for each InlineTarget)
     * haven't been resolved to the MethodNodes they target.
     * This method takes care of that, setting `InlineTarget.callee` and `InlineTarget.owner` as a side-effect.
     *
     * can-multi-thread, provided each callsite.owner has been entered as TypeName in Names.
     * */
    def populate() {
      if(!Util.isReadyForAnalyzer(host)) {
        Util.computeMaxLocalsMaxStack(host)
      }
      for(c <- candidates) {
        c.populate()
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

  /**
   *  An inlining request, given by a callsite and items for error reporting.
   *
   *  @param callsite for which inlining has been requested
   *  @param cunit    for error reporting
   *  @param pos      for error reporting
   *
   * */
  final class InlineTarget(val callsite: MethodInsnNode, val cunit: CompilationUnit, val pos: Position) {

    var callee: MethodNode = null // the concrete callee denoted by the callsite
    var owner:  ClassNode  = null // the class declaring the callee

    def populate() {
      val ownerBT = lookupRefBType(callsite.owner)
      // `null` usually indicates classfile wasn't found and thus couldn't be parsed. TODO warning?
      val mnAndOwner = codeRepo.getMethodOrNull(ownerBT, callsite.name, callsite.desc)
      if(mnAndOwner != null) {
        callee = mnAndOwner.mnode
        owner  = mnAndOwner.owner
        if(!Util.isReadyForAnalyzer(callee)) {
          Util.computeMaxLocalsMaxStack(callee)
        }
      }
    }

    def calleeId: String = { owner.name + "::" + callee.name + callee.desc }

    def warn(msg: String) = cunit.inlinerWarning(pos, msg)

  }

  object inlineTargetOrdering extends scala.math.Ordering[InlineTarget] {
    def compare(x: InlineTarget, y: InlineTarget): Int = {
      x.hashCode().compare(y.hashCode())
    }
  }

  /**
   * WholeProgramAnalysis needs ClassNodes to be available for all classes being compiled
   * (preparing those ClassNodes is the job of GenBCode's Worker1, with queue q2 being filled as a result).
   * However, `WholeProgramAnalysis.inlining()` does not consume ClassNodes from q2
   * but from a queue of CallGraphNodes (BCodeOptInter.cgns) that is populated during PlainClassBuilder's genDefDef().
   *
   */
  final class WholeProgramAnalysis {

    import asm.tree.analysis.{Analyzer, BasicValue, BasicInterpreter}

    val unreachCodeRemover = new asm.optimiz.UnreachableCode

    /**
     *  TODO documentation
     *
     *  must-single-thread due to `inlining()`
     *
     **/
    def optimize() {
      assertPipeline1Done(
        "Before Inlining starts, all ClassNodes being compiled should be available to detect and break inlining cycles, " +
        "ie pipeline-1 should be finished."
      )
      ifDebug { closuRepo.checkDClosureUsages() }
      privatizables.clear()
      inlining()
      for(priv <- privatizables; shioMethod <- priv._2) { Util.makePrivateMethod(shioMethod) }
      privatizables.clear()
    }

    /**
     * shio methods are collected as they are built in the `privatizables` map, grouped by their ownning class.
     * (That class also owns what used to be the endpoint of the delegating-closure that was inlined).
     *
     * shio methods spend most of their time as public methods, so as not to block method-inlining
     * (they're synthetically generated, thus it would come as a surprise if they required attention from the developer).
     * However, in case no method-inlining transplanted them to another class, they are made private as initially intended.
     * */
    private val privatizables = new MethodsPerClass

    private class MethodsPerClass extends mutable.HashMap[BType, List[MethodNode]] {

      def track(k: ClassNode, v: MethodNode) { track(lookupRefBType(k.name), v) }
      def track(k: BType,     v: MethodNode) { put(k, v :: getOrElse(k, Nil)) }

      /**
       *  It's ok trying to untrack a method that's not being tracked. If in doubt, call untrack()
       * */
      def untrack(k: BType, v: MethodNode) {
        val v2 = getOrElse(k, Nil) filterNot { _ eq v }
        if(v2.isEmpty) { remove(k)  }
        else           { put(k, v2) }
      }

      /**
       *  It's ok trying to untrack a method that's not being tracked. If in doubt, call untrack()
       * */
      def untrack(k: BType, methodName: String, methodDescr: String) {
        val v2 = getOrElse(k, Nil) filterNot { mn => (mn.name == methodName) && (mn.desc == methodDescr) }
        if(v2.isEmpty) { remove(k)  }
        else           { put(k, v2) }
      }

    } // end of class MethodsPerClass

    // -------------------------------------------------------------------------------
    // ------------------------------- inlining rounds -------------------------------
    // -------------------------------------------------------------------------------

    /**
     *  Performs closure-inlining and method-inlining, by first breaking any cycles
     *  over the "inlined-into" relation (see local method `isReachable()`).
     *  Afterwards,
     *    - `WholeProgramAnalysis.inlineMethod()`   takes care of method-inlining
     *    - `WholeProgramAnalysis.inlineClosures()` of closure-inlining
     *
     *  must-single-thread
     *
     **/
    private def inlining() {

      isInliningDone = true

      // not that anyone is running yet dead-code elimination before inlining, just future-proofing for that case.
      for(cgn <- cgns) {
        cgn.hiOs  = cgn.hiOs  filter { it: InlineTarget => cgn.host.instructions.contains(it.callsite) }
        cgn.procs = cgn.procs filter { it: InlineTarget => cgn.host.instructions.contains(it.callsite) }
      }

      /*
       * The MethodNode for each callsite to an @inline method is found via `CallGraphNode.populate()`,
       * if necessary by parsing bytecode (ie the classfile given by a callsite's `owner` field is parsed).
       * This is safe because by the time `WholeProgramAnalysis.inlining()` is invoked
       * all classes being compiled have been put in `codeRepo.classes` already.
       * Not finding a class there means it has to be parsed.
       */
      val mn2cgn = mutable.Map.empty[MethodNode, CallGraphNode]
      for(cgn <- cgns) {
        cgn.populate()
        assert(cgn.isRepOK)
        mn2cgn += (cgn.host -> cgn)
      }

          /**
           * @return true iff there's a chain of inline-requests starting at `start` that contains `goal`
           * */
          def isReachable(start: MethodNode, goal: MethodNode, visited: Set[MethodNode]): Boolean = {
            (start eq goal) ||
            (visited contains goal) || {

              val directCallees: Set[MethodNode] = {
                mn2cgn.get(start) match {
                  case Some(startCGN) => startCGN.directCallees
                  case _              => Set.empty
                }
              }
              (directCallees contains goal) || {
                val visited2 = (visited ++ directCallees)

                directCallees exists { d => isReachable(d, goal, visited2) }
              }

            }
          }

      for(cgn <- cgns) {
        cgn.hiOs  = cgn.hiOs  filterNot { it: InlineTarget => isReachable(it.callee, cgn.host, Set.empty) }
        cgn.procs = cgn.procs filterNot { it: InlineTarget => isReachable(it.callee, cgn.host, Set.empty) }
      }

      /**
       *  It only remains to visit the elements of `cgns` in an order that ensures
       *  a CallGraphNode has stabilitzed by the time it's inlined into a host method.
       *  "A CallGraphNode has stabilized" means all inlinings have been performed inside it,
       *  where those inlinings were based on callees that were themselves already stabilized.
       */
      val remaining = mutable.Set.empty[CallGraphNode]
      remaining ++= cgns.toList
      while(remaining.nonEmpty) {
        val leaves = remaining.filter( cgn => cgn.candidates.forall( c => !mn2cgn.contains(c.callee) || !remaining.contains(mn2cgn(c.callee)) ) )
        assert(leaves.nonEmpty, "Otherwise loop forever")
        inliningRound(leaves)
        remaining --= leaves
      }

    } // end of method inlining()

    /**
     *  TODO leaves are independent from each other, use task-parallelism thus making not just -o2 faster but also
     *       -o3 and -o4 (inlining is the bottleneck, -o3 and -o4 are relatively fast).
     *
     *  @param leaves set of inlining requests that are independent from each other.
     *
     * */
    private def inliningRound(leaves: collection.Set[CallGraphNode]) {

      leaves foreach { leaf => inlineCallees(leaf) }

    }

    /**
     *  Perform inlinings in a single method (given by `CallGraphNode.host`)
     *  of the callees given by `CallGraphNode.procs` and `CallGraphNode.hiOs`.
     *
     *  @param leaf a set of inlining-requests, both for methods and closures, for callsites in `leaf.host`
     *
     *  must-single-threadd
     */
    private def inlineCallees(leaf: CallGraphNode) {

      // debug: `Util.textify(leaf.host)` can be used to record (before and after) what the host-method looks like.

      //----------------------------------------------------------------------
      // Part 1 of 4: Dead-code elimination, reporting about callsites that are dead
      //----------------------------------------------------------------------

          def logDead(callsite: MethodInsnNode) {
            log(
              s"Dead-code elimination in method ${methodSignature(leaf.hostOwner, leaf.host)} " +
              s"has removed a callsite that was marked for inlining, callsite ${Util.textify(callsite)}"
            )
          }

      {
        // UnreachableCode eliminates null frames (which complicate further analyses).
        Util.computeMaxLocalsMaxStack(leaf.host)
        unreachCodeRemover.transform(leaf.hostOwner.name, leaf.host)
        val (remainingProcs, deadCodeProcs) = leaf.procs partition { proc => leaf.host.instructions.contains(proc.callsite) }
        for(proc <- deadCodeProcs) { logDead(proc.callsite) }
        leaf.procs = remainingProcs
        val (remainingHiOs, deadHiOs) = leaf.hiOs partition { hiO => leaf.host.instructions.contains(hiO.callsite) }
        for(hiO <- deadHiOs) { logDead(hiO.callsite) }
        leaf.hiOs = remainingHiOs
      }

      //----------------------------------------------------------------------
      // Part 2 of 4: Type-Flow Analysis to determine non-nullness of receiver
      //----------------------------------------------------------------------

      val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
      tfa.analyze(leaf.hostOwner.name, leaf.host)
      // looking up in array `frames` using the whatever-then-current index of `insn` would assume the instruction list hasn't changed.
      // In general that doesn't hold after inlineMethod() or inlineClosures()
      // Instead of re-running the Type-Flow Analysis, for the purposes of inlining it's ok to have at hand for a callsite
      // its frame as it was when the analysis was computed (because that frame stays the same irrespective of inlinings performed).
      val tfaFrameAt: Map[MethodInsnNode, asm.tree.analysis.Frame[TFValue]] = {
         leaf.candidates
        .filter(it => leaf.host.instructions.contains(it.callsite))
        .map(it => it.callsite -> tfa.frameAt(it.callsite).asInstanceOf[asm.tree.analysis.Frame[TFValue]]).toMap
      }

      //-----------------------------
      // Part 3 of 4: method-inlining
      //-----------------------------

      leaf.procs foreach { proc =>

        val hostOwner    = leaf.hostOwner.name
        val frame        = tfaFrameAt(proc.callsite)
        val isRcvNonNull = isReceiverKnownNonNull(frame, proc.callsite)

        val inlineMethodOutcome = inlineMethod(
          hostOwner,
          leaf.host,
          proc.callsite,
          frame,
          proc.callee, proc.owner,
          doTrackClosureUsage = true,
          isDefinitelyNonNull = isRcvNonNull
        )
        inlineMethodOutcome foreach proc.warn

        val success = inlineMethodOutcome.isEmpty
        logInlining(
          success, hostOwner, leaf.host, proc.callsite, isHiO = false,
          isRcvNonNull,
          proc.callee, proc.owner
        )

      }
      leaf.procs = Nil

      //------------------------------
      // Part 4 of 4: closure-inlining
      //------------------------------

      leaf.hiOs foreach { hiO =>

        val callsiteTypeFlow = tfaFrameAt(hiO.callsite)
        assert(callsiteTypeFlow != null,
          s"Most likely dead-code found in method ${methodSignature(leaf.hostOwner, leaf.host)} " +
          s"because at instruction ${Util.textify(hiO.callsite)} (at index ${leaf.host.instructions.indexOf(hiO.callsite)}}) " +
           "no frame is computed by type-flow analysis. Here's the complete bytecode of that method " + Util.textify(leaf.host)
        )

        val hasNonNullReceiver = isReceiverKnownNonNull(callsiteTypeFlow, hiO.callsite)

        val outecome = inlineClosures(
          leaf.hostOwner,
          leaf.host,
          callsiteTypeFlow,
          hiO,
          hasNonNullReceiver
        )
        val success = outecome.nonEmpty

        logInlining(
          success, leaf.hostOwner.name, leaf.host, hiO.callsite, isHiO = true,
          hasNonNullReceiver,
          hiO.callee, hiO.owner
        )
        if(success) {
          log(outecome.get)
        }

      }
      leaf.hiOs = Nil

      ifDebug {
        val da = new Analyzer[BasicValue](new asm.tree.analysis.BasicVerifier)
        da.analyze(leaf.hostOwner.name, leaf.host)
      }

    } // end of method inlineCallees()

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
     *          without forgetting to empty all the stack slots except stack-top right before jumping to that single-exit)
     *   (c) copying the debug info from the callee's over to the host method
     *   (d) re-computing the maxLocals and maxStack of the host method.
     *   (e) return None (this indicates success).
     *
     * Inlining is considered unfeasible in four cases, summarized below and described in more detail on the spot:
     *   (a.0) callee is a synchronized method
     *   (a.1) due to the possibility of the callee clearing the operand-stack when entering an exception-handler
     *   (a.2) inlining would lead to illegal access errors.
     *   (a.3) calee returns scala.runtime.Nothing$ , which means it'll throw an exception
     *         (s.r.Nothing$ looks like an object to the type-flow analysis).
     *
     * @param hostOwner   internal name of the class declaring the host method
     * @param host        method containing a callsite for which inlining has been requested
     * @param callsite    invocation whose inlining is requested.
     * @param frame       informs about stack depth at the callsite
     * @param callee      actual method-implementation that will be dispatched at runtime.
     * @param calleeOwner class that declares callee
     * @param doTrackClosureUsage TODO documentation
     *
     * @return None iff method-inlining was actually performed,
     *         Some(diagnostics) iff the inlining is unfeasible.
     *
     */
    def inlineMethod(hostOwner:     String,
                     host:          MethodNode,
                     callsite:      MethodInsnNode,
                     frame:         asm.tree.analysis.Frame[TFValue],
                     callee:        MethodNode,
                     calleeOwner:   ClassNode,
                     doTrackClosureUsage: Boolean,
                     isDefinitelyNonNull: Boolean): Option[String] = {

      assert(callee != null)
      assert(callsite.name == callee.name)
      assert(callsite.desc == callee.desc)
      assert(!Util.isConstructor(callee))

      if(!host.instructions.contains(callsite)) {
        val diagnostics =
           "That's strange. A callsite that was going to be inlined has been marked as dead-code. " +
          s"Callsite: ${insnPos(callsite, host)} , in method ${methodSignature(hostOwner, host)}"
        return Some(diagnostics)
      }

      /*
       * Situation (a.0) under which method-inlining is unfeasible: synchronized callee.
       */
      if(Util.isSynchronizedMethod(callee)) {
        return Some(s"Method-inlining failed because ${methodSignature(calleeOwner, callee)} is synchronized.")
      }

      /*
       * Situation (a.1) under which method-inlining is unfeasible: In case both conditions below hold:
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
          return Some(
            s"The operand stack may be cleared on entering an exception-handler in ${methodSignature(calleeOwner, callee)} , and " +
            s"the stack at the callsite in ${methodSignature(hostOwner, host)} contains more values than args expected by the callee."
          )
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
       * (the GenBCode infrastructure standardizes on TypeNames for lookups).
       * The utility below takes care of creating TypeNames for those descriptors and internal names.
       * Even if inlining proves unfeasible, those TypeNames won't cause any harm.
       *
       * TODO why weren't those TypeNames entered as part of parsing callee from bytecode?
       *      After all, we might want to run e.g. Type-Flow Analysis on external methods before inlining them.
       */
      codeRepo.registerUnseenTypeNames(body) // must-single-thread

      val hostOwnerBT = lookupRefBType(hostOwner)

      val illegalAccessInsn = allAccessesLegal(body, hostOwnerBT)
      if(illegalAccessInsn != null) {
        return Some(
          s"Callee ${methodSignature(calleeOwner, callee)} contains instruction \n${Util.textify(illegalAccessInsn)} " +
          s"that would cause IllegalAccessError from class $hostOwner"
        )
      }

      val calleeMethodType = BType.getMethodType(callee.desc) // must-single-thread

      /*
       * Situation (a.3) under which method-inlining is unfeasible: callee has Nothing type.
       */
      if(calleeMethodType.getReturnType.isNothingType) {
        return Some(s"Method-inlining failed because ${methodSignature(calleeOwner, callee)} has Nothing type.")
      }

      // By now it's a done deal that method-inlining will be performed. There's no going back.

      // each local-var access in `body` is shifted host.maxLocals places
      for(bodyInsn <- bodyInsns; if bodyInsn.getType == AbstractInsnNode.VAR_INSN) {
        val lvi = bodyInsn.asInstanceOf[VarInsnNode]
        lvi.`var` += host.maxLocals
      }

      // add a STORE instruction for each expected argument, including for THIS instance if any.
      val argStores   = new InsnList
      var nxtLocalIdx = host.maxLocals
      if(Util.isInstanceMethod(callee)) {
        if(!isDefinitelyNonNull) {
          // similar in purpose to JDK7's j.u.Objects.requireNonNull, see SI-5850
          argStores.add(new InsnNode(Opcodes.DUP))
          val nonNullL  = new asm.Label
          val nonNullLN = new asm.tree.LabelNode(nonNullL)
          nonNullL.info = nonNullLN
          argStores.add(new JumpInsnNode(Opcodes.IFNONNULL, nonNullLN))
          argStores.add(new InsnNode(Opcodes.ACONST_NULL))
          argStores.add(new InsnNode(Opcodes.ATHROW))
          argStores.add(nonNullLN)
        }
        argStores.add(new VarInsnNode(Opcodes.ASTORE, nxtLocalIdx))
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
            val retVarIdx      = host.maxLocals + callee.maxLocals
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
            for(calleeInsn <- insnArr; if Util.isRETURN(calleeInsn)) {
              val retInsn = calleeInsn.asInstanceOf[InsnNode]
              val frame   = ca.frameAt(retInsn) // NPE means dead-code wasn't removed from the callee before calling inlineMethod
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

      if(doTrackClosureUsage) {
        checkTransplantedAccesses(body, hostOwnerBT)
      }

      host.instructions.insert(callsite, body) // after this point, body.isEmpty (an ASM instruction can be owned by a single InsnList)
      host.instructions.remove(callsite)

      // let the host know about the debug info of the callee
      host.localVariables.addAll(Util.clonedLocalVariableNodes(callee, labelMap, callee.name + "_"))
      host.tryCatchBlocks.addAll(Util.clonedTryCatchBlockNodes(callee, labelMap))

      // the host's local-var space grows by the local-var space of the callee, plus another local-var in case hasReturnValue
      Util.computeMaxLocalsMaxStack(host)
      assert(host.maxLocals >= nxtLocalIdx) // TODO why not == ? Likely because a RETURN in callee adds no extra var in host for result, while IRETURN etc do.

      None

    } // end of method inlineMethod()

    private def logInlining(success:   Boolean,
                            hostOwner: String,
                            host:      MethodNode,
                            callsite:  MethodInsnNode,
                            isHiO:     Boolean,
                            isReceiverKnownNonNull: Boolean,
                            hiO:       MethodNode,
                            hiOOwner:  ClassNode) {

      val kind    = if(isHiO)   "closure-inlining "  else "method-inlining "
      val leading = if(success) "Successful " + kind else "Failed " + kind

      log(leading + s"Callsite: ${insnPos(callsite, host)} , in method ${methodSignature(hostOwner, host)}")

      if(!success) {
        debuglog(s"Bytecode of callee, declared by ${hiOOwner.name} \n" + Util.textify(hiO))
      }

    } // end of method logInlining()

    /**
     * Situation (a.2) under which method-inlining is unfeasible:
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
     *  @param body instructions that will be inlined in a method in class `here`
     *  @param here class from which accesses given by `body` will take place.
     *
     *  @return the first instruction found in `body`
     *          that would result in java.lang.IllegalAccessError if used from class `here`.
     *
     */
    private def allAccessesLegal(body: InsnList, here: BType): AbstractInsnNode = {

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

          def memberAccess(flags: Int, thereOwner: BType): Boolean = {
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
                  isStatic || sameLineage(thereOwner)
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

          case ti: TypeInsnNode  => isAccessible(lookupRefBType(ti.desc), here)

          case fi: FieldInsnNode =>
            val fowner: BType = lookupRefBType(fi.owner)
            val fn: FieldNode = codeRepo.getFieldOrNull(fowner, fi.name, fi.desc)
            (fn != null) && memberAccess(fn.access, fowner)

          case mi: MethodInsnNode =>
            val thereSymRef: BType  = lookupRefBType(mi.owner)
            val mAccess: Option[Int] = codeRepo.getMethodAccess(thereSymRef, mi.name, mi.desc)
            mAccess.nonEmpty && memberAccess(mAccess.get, thereSymRef)

          case ivd: InvokeDynamicInsnNode => false // TODO

          case ci: LdcInsnNode =>
            ci.cst match {
              case t: asm.Type => isAccessible(lookupRefBType(t.getInternalName), here)
              case _           => true
            }

          case ma: MultiANewArrayInsnNode =>
            val et = descrToBType(ma.desc).getElementType
            if(et.hasObjectSort) isAccessible(et, here)
            else true

          case _ => true
        }
        if(!isLegal) {
          return insn
        }
      }

      null // stands for "all accesses legal"

    } // end of method allAccessesLegal()

    /**
     * See also method `allAccessesLegal()`
     *
     * Quoting from the JVMS (our terminology: `there` stands for `C`; `here` for `D`):
     *
     *  5.4.4 Access Control
     *
     *  A class or interface C is accessible to a class or interface D if and only if either of the following conditions is true:
     *    (cond A1) C is public.
     *    (cond A2) C and D are members of the same runtime package (Sec 5.3).
     */
    private def isAccessible(there: BType, here: BType): Boolean = {
      if(!there.isNonSpecial) true
      else if (there.isArray) isAccessible(there.getElementType, here)
      else {
        assert(there.hasObjectSort, "not of object sort: " + there.getDescriptor)
        (there.getRuntimePackage == here.getRuntimePackage) || exemplars.get(there).isPublic
      }
    }

    private def allExceptionsAccessible(tcns: java.util.List[TryCatchBlockNode], here: BType): Boolean = {
      JListWrapper(tcns).forall( tcn => (tcn.`type` == null) || isAccessible(lookupRefBType(tcn.`type`), here) )
    }

    private def allLocalVarTypesAccessible(lvns: java.util.List[LocalVariableNode], here: BType): Boolean = {
      JListWrapper(lvns).forall( lvn => {
        val there = descrToBType(lvn.desc)

        there.isValueType || isAccessible(there, here)
      } )
    }

    /**
     * This method inlines the invocation of a "higher-order method" and
     * stack-allocates the anonymous closures received as arguments.
     *
     * "Stack-allocating" in the sense of "scalar replacement of aggregates" (see also "object fusion").
     * This can always be done for closures converted in UnCurry via `closureConversionModern()`
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
     * "Regarded as a loop header" because we'd like the JIT compiler to pick that code section for compilation.
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
     *                    - via `closureConversionModern()` there are no additional closure-methods.
     *                    - via `closureConversionTraditional()`  those methods that were local to the source-level apply()
     *                      also become closure-methods after lambdalift.
     *
     * closure-constructor: a sequence of assignments to initialize the (from then on immutable) closure-state by copying arguments' values.
     *                      The first such argument is always the THIS of the invoker,
     *                      which becomes the $outer value from the perspective of the closure-class.
     *
     *
     * Preconditions
     * -------------
     *
     * In order to stack-allocate a particular closure passed to Hi-O,
     * the closure in question should not escape from Hi-O (a necessary condition).
     * There's in fact a whole cascade of prerequisites to check,
     * desribed in detail in helper methods `survivors1()` to `survivors3()`,
     * with some yet more pre-conditions being check in `ClosureClassUtil.isRepOK()`.
     *
     * Rewriting mechanics
     * -------------------
     *
     * Provided all pre-conditions have been satisfied, `StaticHiOUtil.buildStaticHiO()` is tasked with
     * preparing a MethodNode that will be invoked instead of hi-O. That method is the last one to have veto power.
     * If successful, it only remains for `StaticHiOUtil.rewriteHost()` to patch `host` to change the target of
     * the original callsite invocation, as well as adapt its arguments.
     *
     * @param hostOwner        the class declaring the host method.
     *                         Upon successful closure-inling, a "static-HiO" ("shio") method is added to hostOwner.
     * @param host             the method containing a callsite for which inlining has been requested
     * @param callsiteTypeFlow the type-stack reaching the callsite. Useful for knowing which args are closure-typed.
     * @param inlineTarget     inlining request (includes: callsite, callee, callee's owner, and error reporting)
     *
     * @return Some(detailedMessage) iff inlining was actually performed, None otherwise.
     *
     * must-single-thread
     *
     */
    private def inlineClosures(hostOwner:        ClassNode,
                               host:             MethodNode,
                               callsiteTypeFlow: asm.tree.analysis.Frame[TFValue],
                               inlineTarget:     InlineTarget,
                               hasNonNullReceiver: Boolean): Option[String] = {

      // invocation of a higher-order method (taking one or more closures) whose inlining is requested.
      val callsite: MethodInsnNode = inlineTarget.callsite
      // the actual implementation of the higher-order method that will be dispatched at runtime
      val hiO:      MethodNode     = inlineTarget.callee
      // the Classnode where callee is declared.
      val hiOOwner: ClassNode      = inlineTarget.owner

      codeRepo.registerUnseenTypeNames(hiO.instructions) // must-single-thread

      if(Util.isSynchronizedMethod(hiO)) {
        inlineTarget.warn(s"Closure-inlining failed because ${inlineTarget.calleeId} is synchronized.")
        return None
      }

      val illegalAccessInsn = allAccessesLegal(hiO.instructions, lookupRefBType(hostOwner.name))
      if(illegalAccessInsn != null) {
        inlineTarget.warn(
          s"Closure-inlining failed because ${inlineTarget.calleeId} contains instruction \n${Util.textify(illegalAccessInsn)} " +
          s"that would cause IllegalAccessError from class ${hostOwner.name}"
        )
        return None
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
        /*
         * Example,
         *   callsite `global.log`
         *   in `def log(msg: => AnyRef) { global.log(msg) }`
         * will have empty closureTypedArgs because it receives a Function0, not an anon-closure-class.
         * We try to overcome that by method-inlining (not closure-inlining) that callsite.
         * Doing so may unblock closure-inlining of the closure(s) passed to `host` (itself a higher-order method).
         *
         */
        val asMethodInlineOutcome =
          inlineMethod(
            hostOwner.name, host,
            callsite, callsiteTypeFlow,
            hiO, hiOOwner,
            doTrackClosureUsage = true,
            isDefinitelyNonNull = false
          )

        asMethodInlineOutcome match {

          case Some(diagnostics) =>
            inlineTarget.warn(diagnostics)
            return None

          case None =>
            val quickOptimizer = new QuickCleanser(hostOwner)
            quickOptimizer.basicIntraMethodOpt(host)
            Util.computeMaxLocalsMaxStack(host)
            return Some(
              "Not really ''successful closure-inlining'' but inlining anyway: the callsite receives a scala.FunctionX, not a closure-class. " +
              "Performed method-inlining (not closure-inlining) at that callsite, hoping to unblock closure-inlining of the anon-closure(s) passed to " +
              methodSignature(hostOwner, host) +
              " (itself a higher-order method)"
            )

        }

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
           * However it protects against any non-standard transform that messes up with preconds required for correctness.
           *
           * `survivors2()` goes over the formal params in `survivors1()`, picking those that have a single producer,
           * such that the value thus produced is the only actual for the param in question.
           *
           * Given that the type of the actual fulfills Tracked.isClosureClass,
           * the ClassNode of that type can be found in codeRepo.classes (it's being compiled in this run).
           *
           * @return a map with an entry for each hiO method-param that takes a closure,
           *         where an entry maps the position of the method-param to a closure class.
           */
          def survivors2(): Map[Int, ClassNode] = {

            // if cpHost were to be hoisted out of this method, cache `cpHost.frameAt()` before hiOs are inlined.
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
        inlineTarget.warn(
          s"Can't perform closure-inlining because in ${methodSignature(hostOwner, host)} different closures may arrive at the same argument position."
        )
        return None
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
                 *  and if so return the MethodNode for that apply(). Otherwise null.
                 *
                 *  @param closureClass     class realizing the closure of interest
                 *  @param localVarIdxHiO   local-var in hiO (a formal param) whose value is the closure of interest
                 *  @param closureArgUsages instructions where the closure is used as input
                 */
                def areAllApplyCalls(closureClass:      ClassNode,
                                     localVarIdxHiO:    Int,
                                     closureArgUsages:  collection.Set[AbstractInsnNode],
                                     formalParamPosHiO: Int): MethodNode = {

                      def warn(reason: String) {
                        inlineTarget.warn(
                          s"Can't stack-allocate the closure passed at argument position $formalParamPosHiO because $reason"
                        )
                      }

                  // (1) all usages are invocations
                  if(closureArgUsages.exists(insn => insn.getType != AbstractInsnNode.METHOD_INSN)) {
                    warn(s"not all of its usages in ${inlineTarget.calleeId} are invocations of the closure's apply() method.")
                    return null
                  }

                  // (2) moreover invocations of one and the same method
                  if(closureArgUsages.isEmpty) {
                    warn(s"no invocations were found in ${inlineTarget.calleeId} of the closure's apply() method.")
                    return null
                  }
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
                      warn(s"one or more methods other than apply() are called on it in ${inlineTarget.calleeId}")
                      return null
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

                    if(passesClosureAsArgument) {
                      warn(s"${inlineTarget.calleeId} passes the closure as argument, thus letting it escape (to a method not marked @inline).")
                      return null
                    }
                    if(!isDispatchedOnClosure) {
                      warn(s"${inlineTarget.calleeId} contains a closure usage other than as receiver of apply().")
                      return null
                    }
                  }

                  // (4) whether it's actually an apply or specialized-apply invocation
                  val arity = BType.getMethodType(fst.desc).getArgumentCount
                  if(arity > definitions.MaxFunctionArity) {
                    warn("the callee invokes apply() on the closure with more than " + definitions.MaxFunctionArity + " arguments.")
                    return null
                  }

                  // all checks passed, look up applyMethod
                  val closureClassBType = lookupRefBType(closureClass.name)
                  val tentative = codeRepo.getMethodOrNull(closureClassBType, fst.name, fst.desc)
                  val applyMethod =
                    if(tentative == null) { null }
                    else { tentative.mnode }

                  if(applyMethod == null) {
                    warn(s"${inlineTarget.calleeId} invokes apply() on the closure, but the bytecode for that method couldn't be found.")
                  }

                  applyMethod
                }

            for (
              (formalParamPosHiO, closureClass) <- closureClassPerHiOFormal;
              localVarIdxHiO = mtHiO.convertFormalParamPosToLocalVarIdx(formalParamPosHiO, isInstanceMethod);
              closureArgUsages: Set[AbstractInsnNode] = JSetWrapper(cpHiO.consumersOfLocalVar(localVarIdxHiO)).toSet;
              applyMethod = areAllApplyCalls(closureClass, localVarIdxHiO, closureArgUsages, formalParamPosHiO);
              if applyMethod != null
            ) yield ClosureUsages(
              formalParamPosHiO,
              localVarIdxHiO,
              closureClass,
              applyMethod,
              closureArgUsages map (_.asInstanceOf[MethodInsnNode])
            )
          }

      val (closureClassUtils, failedAttempts) =
        (survivors3().toArray.map { cu => ClosureClassUtil(cu) }) partition { ccu => ccu.isRepOK }

      for(fa <- failedAttempts) { inlineTarget.warn(fa.diagnostics) }

      if(closureClassUtils.isEmpty) {
        return None
      }

      val shioUtil = StaticHiOUtil(hiO, closureClassUtils)
      val staticHiO: MethodNode = shioUtil.buildStaticHiO(hostOwner, callsite, inlineTarget, hasNonNullReceiver)
      if(staticHiO == null) { return None }
      assert(Util.isPublicMethod(staticHiO), "Not a public method: " + methodSignature(hostOwner, staticHiO))
      if(!shioUtil.rewriteHost(hostOwner, host, callsite, staticHiO, inlineTarget)) {
        return None
      }

      val enclClass = lookupRefBType(hostOwner.name)
      checkTransplantedAccesses(staticHiO.instructions, enclClass)

      hostOwner.methods.add(staticHiO)
      privatizables.track(hostOwner, staticHiO)
      for(ccu <- closureClassUtils) {
        val dclosure: BType = lookupRefBType(ccu.closureClass.name)
        if(closuRepo.isDelegatingClosure(dclosure)) {

          val mc = closuRepo.masterClass(dclosure)
          if(mc != enclClass) {
            log(
              s"DClosure usage in non-master: a static-HiO method added to class ${hostOwner.name} " +
              s"(resulting from inlining closure $dclosure) invokes that closure's endpoint method (which is declared in $mc)"
            )
            assert(closuRepo.isNonMasterUser(dclosure, enclClass))
          }

          // once inlined, a dclosure used only by its master class loses its "dclosure" status
          if(!closuRepo.hasMultipleUsers(dclosure)) {
            Util.makePrivateMethod(closuRepo.endpoint.get(dclosure).mnode)
            closuRepo.retractAsDClosure(dclosure)
          }

        }
      }

      {
        val elidedSize     = closureClassUtils.size
        val elidedListing  =
          for(idx <- 0 to (elidedSize - 1))
          yield { s"(${idx + 1}} of $elidedSize): ${closureClassUtils(idx).closureClass.name}" }
        val detailedMessage =
          s"\tFor the closure inlining just mentioned, added static-HiO method: ${methodSignature(hostOwner, staticHiO)}. " +
           "Elided anon-closures: " + elidedListing.mkString(" , ")

        Some(detailedMessage)
      }
    } // end of method inlineClosures

    /**
     *
     * */
    private def checkTransplantedAccesses(body: InsnList, enclClass: BType) {

      /*
       * An invocation to a shio method declared in a class other than the new home of the callsite (enclClass)
       * forces the shio method in question to remain public.
       * */
      body foreachInsn { insn =>
        insn match {
          case mi: MethodInsnNode =>
            val calleeOwnerBT = lookupRefBType(mi.owner)
            if(calleeOwnerBT != enclClass) {
              // it's ok to try to untrack a method that's not being tracked
              privatizables.untrack(calleeOwnerBT, mi.name, mi.desc)
            }
          case _ => ()
        }
      }

      /*
       * In case `insn` denotes a dclosure instantiation or endpoint invocation
       * and `enclClass` isn't the master class of that dclosure, note this fact `nonMasterUsers`.
       * */
      body foreachInsn { insn => closuRepo.trackClosureUsageIfAny(insn, enclClass) }

    }

    /**
     *  For a given pair (hiO method, closure-argument) an instance of ClosureUsages
     *  records the apply() invocations inside hiO for that closure-argument.
     *
     *  @param formalParamPosHiO zero-based position in the formal-params-list of hiO method
     *  @param localVarIdxHiO    corresponding index in the locals-array of hiO method
     *                           (in general different from formalParamPosHiO due to JVM-type-sizes)
     *  @param closureClass      final class of the closure (ie not e.g. Function1 but an anon-closure-class)
     *  @param applyMethod       the apply method invoked inside hiO (which in turn may invoke another).
     *  @param usages            invocations in hiO of closureClass' applyMethod.
     *                           Allows finding out the instruction producing receiver and arguments.
     */
    private case class ClosureUsages(
      formalParamPosHiO: Int,
      localVarIdxHiO:    Int,
      closureClass:      ClassNode,
      applyMethod:       MethodNode,
      usages:            Set[MethodInsnNode]
    )

    /**
     *  Query methods that dig out information hidden in the structure of a closure-class.
     */
    private case class ClosureClassUtil(closureUsages: ClosureUsages) {

      def closureClass: ClassNode = closureUsages.closureClass

      val constructor: MethodNode = {
        var result: MethodNode = null
        val iter = closureClass.methods.iterator()
        while(iter.hasNext) {
          val nxt = iter.next()
          if(nxt.name == "<init>") {
            assert(result == null, s"duplicate <init> method found in closure-class: ${closureClass.name}")
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
                // for outer-param, don't count IFNULL, or IFNONNULL, (in general any jump instruction) as consumer
                val consumerIter = consumers.iterator()
                var stop = false
                while(consumerIter.hasNext && !stop) {
                  val cnext = consumerIter.next
                  if(cnext.getType == AbstractInsnNode.JUMP_INSN) {
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
          ) yield (fieldName -> (localVarIdx - 1))

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

      /**
       *  As part of building staticHiO, closure-usages in hiO are replaced by either:
       *    (a) self-contained code snippets; or
       *    (b) invocation to the delegate created during `closureConversionModern()`
       *
       *  In both cases the snippet of instructions to paste (let's call it "stub") should:
       *    (c) avoid using the closure's THIS; and
       *    (d) consume from the operand-stack what the `applyMethod` invocation used to consume, and
       *        leave on exit what `applyMethod()` used to return.
       *
       *  In order to implement the above, it's way easier if `staticHiO` doesn't have to
       *  chase invocation chains like:
       *
       *    (1) First into "bridge-style apply()"
       *
       *          final < bridge > < artifact > def apply(v1: Object): Object = {
       *            apply(scala.Int.unbox(v1));
       *            scala.runtime.BoxedUnit.UNIT
       *          };
       *
       *    (2) Which in turn invokes a "forwarding apply()"
       *
       *          final def apply(x$1: Int): Unit = apply$mcVI$sp(x$1);
       *
       *    (3) Which finally invokes a "delegate-invoking apply()"
       *
       *          < specialized > def apply$mcVI$sp(v1: Int): Unit = $outer.C$$dlgt1$1(v1);
       *
       *  This utility method returns a fabricated MethodNode, where invocation chains as above have been
       *  collapsed into a self-contained method. In case this is not possible,
       *  this method returns a scala.Util.Left reporting the reason for unfeasibility as a String.
       *
       *  For example, this method returns `Left` for a closure converted by `closureConversionTraditional()`
       *  where the original closure-body contained local-methods that lambdalift turned into
       *  closure-methods. In general it's not always possible to "un-do" all the dependencies on the closure's THIS,
       *  and in the example we don't even try.
       *
       *  Starting from the known `applyMethod`, collapsing involves:
       *    (i)  checking whether THIS doesn't escape. If so, the current method is fine as is.
       *    (ii) in case THIS escapes only as receiver of a (non-recursive) invocation on this closure,
       *         then drill-down into the target. If that target can itself be collapsed,
       *         we collapse it with the current method being visited (as expected,
       *         collapsing a drilled-down method means inlining it into a clone of the current method).
       */
      private def helperStubTemplate(): Either[String, MethodNode] = {

          def escapingThis(mnodeOwner: String, mnode: MethodNode): collection.Set[AbstractInsnNode] = {

                def isClosureStateAccess(insn: AbstractInsnNode) = {
                  insn.getOpcode == Opcodes.GETFIELD && {
                    val fi = insn.asInstanceOf[FieldInsnNode]
                    stateField2constrParam.contains(fi.name)
                  }
                }

            Util.computeMaxLocalsMaxStack(mnode)
            val cpHiO: ProdConsAnalyzer = ProdConsAnalyzer.create()
            cpHiO.analyze(mnodeOwner, mnode)
            for(
              consumer <- JSetWrapper(cpHiO.consumersOfLocalVar(0))
              if !isClosureStateAccess(consumer)
            ) yield consumer
          }

        val closureClassName  = closureUsages.closureClass.name
        val closureClassBType = lookupRefBType(closureClass.name)

            /**
             *  @return Right[MethodNode] fabricated stub for use when building staticHiO
             *          Left[String]      diagnostics message why a stub can't be fabricated
             * */
            def getInnermostForwardee(current: MethodNode, visited0: Set[MethodNode]): Either[String, MethodNode] = {

              val currentId = closureClass.name + "." + current.name + current.desc

              if(!current.tryCatchBlocks.isEmpty) {
                // The instructions of the resulting MethodNode will serve as template to replace closure-usages.
                // TODO warn We can't rule out the possibility of an exception-handlers-table making such replacement non-well-formed.
                return Left(
                  s"Method $currentId contains excepion-handlers. Once inlined, " +
                   " the operand stack may contain more values at that program point than consumed by the closure-usage."
                )
              }
              val escaping = escapingThis(closureClassName, current)
              if(escaping.isEmpty) {
                return Right(current)
              }
              if(escaping.size == 1) {
                escaping.iterator.next() match {

                  case forwarder: MethodInsnNode if forwarder.owner == closureClassName =>
                    val forwardee = codeRepo.getMethod(closureClassBType, forwarder.name, forwarder.desc).mnode
                    val visited   = visited0 + current
                    if(visited.exists(v => v eq forwardee)) {
                      return null // TODO warn recursive invocation chain was detected, involving one or more closure-methods
                    }
                    getInnermostForwardee(forwardee, visited) match {

                      case Right(rewritten) =>
                        val cm: Util.ClonedMethod = Util.clonedMethodNode(current)
                        val clonedCurrent = cm.mnode
                        val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
                        tfa.analyze(closureClassName, current)
                        val clonedForwarder = cm.insnMap.get(forwarder).asInstanceOf[MethodInsnNode]
                        val frame   = tfa.frameAt(clonedForwarder).asInstanceOf[asm.tree.analysis.Frame[TFValue]]
                        val inlineMethodOutcome = inlineMethod(
                          closureClassName,
                          clonedCurrent,
                          clonedForwarder,
                          frame,
                          rewritten, closureUsages.closureClass,
                          doTrackClosureUsage = true,
                          isDefinitelyNonNull = true
                        )
                        return inlineMethodOutcome match {
                          case None                => Right(clonedCurrent)
                          case Some(diagnosticMsg) => Left(diagnosticMsg)
                        }

                      case diagnostics =>
                        return diagnostics
                    }

                  case _ => ()
                }
              }

              Left(s"The closure's THIS value escapes $currentId method")

            } // end of method getInnermostForwardee()

        val result: MethodNode =
          getInnermostForwardee(closureUsages.applyMethod, Set.empty) match {
            case Right(mn)   => mn
            case diagnostics => return diagnostics
          }

        val quickOptimizer = new QuickCleanser(closureClass)
        quickOptimizer.basicIntraMethodOpt(result)
        Util.computeMaxLocalsMaxStack(result)

        if(escapingThis(closureClassName, result).nonEmpty) {
          return Left(
             "In spite of our best efforts, the closure's THIS is used for something that can't be reduced later. " +
            s"In other words, it escapes the methods in class $closureClassName"
          )
        }

        if(!result.tryCatchBlocks.isEmpty) {
          return Left(
            s"The stub computed for class $closureClassName has try-catch block(s), " +
             "and we don't check whether all apply() invocations occur in statement program points " +
             "(as opposed to non-empty-operand-stack program points)."
          )
        }

            def hasMultipleRETURNs: Boolean = {
              var returnSeen = false
              val iter = result.instructions.iterator
              while(iter.hasNext) {
                val nxt = iter.next()
                if(Util.isRETURN(nxt) || (nxt.getOpcode == Opcodes.ATHROW)) {
                  if (returnSeen) { return true; }
                  returnSeen = true
                }
              }

              false
            }

        if(hasMultipleRETURNs) {
          return Left(s"The stub computed for class $closureClassName has multiple exits (ie two or more returns or throw instructions).")
        }

        assert(result.desc == closureUsages.applyMethod.desc)

        Right(result)
      } // end of method helperStubTemplate()

      val stubCreatorOutcome: Either[String, MethodNode] = helperStubTemplate()

      def stubTemplate: MethodNode = stubCreatorOutcome.right.get

      def diagnostics: String = {
        var diags: List[String] = Nil
        if(!areAllFieldsAccountedFor) {
          diags ::= s"Number of closure-state fields should be one less than number of fields in ${closureClass.name}" +
                     "(static field SerialVersionUID isn't part of closure-state)"
        }
        if(stubCreatorOutcome.isLeft) {
          diags ::= stubCreatorOutcome.left.get
        }

        diags.mkString(",\n")
      }

      /**
       * Number of closure-state fields should be one less than number of fields in closure-class
       * (static field SerialVersionUID isn't part of closure-state).
       */
      def areAllFieldsAccountedFor: Boolean = {
        (stateField2constrParam.size == (closureClass.fields.size() - 1)) &&
        (stateField2constrParam.size == field.size)
      }

      def isRepOK: Boolean = {
        areAllFieldsAccountedFor && stubCreatorOutcome.isRight
      }

    } // end of class ClosureClassUtil

    /**
     *  Query methods that help derive a "static hiO method" given a "hiO method".
     *  Most of the rewriting needed to realize closure-inlining is done by `buildStaticHiO()` and `rewriteHost()`.
     *
     *  @param hiO higher-order method for which the closures given by `closureClassUtils`
     *             (closures that `hiO` receives as arguments) are to be stack-allocated.
     *  @param closureClassUtils a subset of the closures that `hiO` expects,
     *                           ie the subset that has survived a plethora of checks about pre-conditions for inlining.
     */
    private case class StaticHiOUtil(hiO: MethodNode, closureClassUtils: Array[ClosureClassUtil]) {

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
       *    (original-local-var-idx-in-HiO -> accumulated-sizes-inluding-constructorParams-for-this-closure)
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
       *  Given a locaVarIdx valid in hiO, returns the localVarIdx (for the same value) in staticHiO.
       *
       *  In principle, this method isn't applicable to closure-receiving params themselves (they simply go away),
       *  but for uniformity in that case returns
       *  the local-var-idx in staticHiO of the param holding the first constructor-param.
       */
      def shiftedLocalIdx(original: Int): Int = {
        assert(original >= 0)
        var i = (closureParamSlack.length - 1)
        while (i >= 0) {
          val Pair(localVarIdx, acc) = closureParamSlack(i)
          if(localVarIdx < original) {
            val result = original + acc
            assert(result >= 0)

            return result
          }
          i -= 1
        }

        original
      }

      /**
       * Quoting from `inlineClosures()`:
       *
       *     Closure inlining results in faster code by specializing a higher-order method
       *     to the particular anonymous closures given as arguments at a particular callsite
       *     (at the cost of code duplication, namely of the Hi-O method, no other code gets duplicated).
       *
       *  The MethodNode built by `buildStaticHiO()` is the "specialized code" referred to above.
       *  The main difficulty is properly shifting local-var-indexes, so that they keep denoting the same values.
       *  Shifting is needed because:
       *    - some formal params have been removed (those for closure-instances), while
       *    - others (zero or more closure-state values) have taken their place, and also because
       *    - the code snippets pasted to replace closure-invocations use local-vars of their own.
       *
       *  The steps to build `staticHiO` are:
       *
       *    (1) pick unique method name
       *
       *    (2) visit `hiO` formal params,
       *        discarding those for stack-allocated closures, and
       *        splicing-in params for closure-state.
       *        Along the way staticHiO's maxLocals is updated. Its initial value was hiO's maxLocals.
       *
       *    (3) now comes putting together the body of staticHiO.
       *        The starting point is a verbatim copy of hiO's InsnList,
       *        ie source-line information will be present (if any).
       *        The exception-handlers table can be copied without changes,
       *        while the entries about visibility ranges of local-vars need shifting.
       *
       *    (4) Those closure-applications still present in the method body can't remain forever.
       *        The contract with `getStubsIterator()` is:
       *            for each closure to inline, give me an iterator of code snippets,
       *            where each code snippet has to be able to cope with the arguments (save for the receiver)
       *            of a usage of that closure (ie of a closure-application).
       *
       *  @return `staticHiO` if preconditions are satisfied. Otherwise null.
       */
      def buildStaticHiO(hostOwner:    ClassNode,
                         callsite:     MethodInsnNode,
                         inlineTarget: InlineTarget,
                         hasNonNullReceiver: Boolean): MethodNode = {

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

        // (2.a) compute method descriptor
        // (2.b) compute initial value of staticHiO's maxLocals (will be updated again once stubs are pasted)
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
        val shiOMethodType = BType.getMethodType(hiOMethodType.getReturnType, formals.reverse.toArray)

        // (3) clone InsnList, get Label map
        val labelMap = Util.clonedLabels(hiO)
        val insnMap  = new java.util.HashMap[AbstractInsnNode, AbstractInsnNode]()
        val body     = Util.clonedInsns(hiO.instructions, labelMap, insnMap)

        // (4) Util.clone TryCatchNodes
        val tcns: java.util.List[TryCatchBlockNode] = Util.clonedTryCatchBlockNodes(hiO, labelMap)
        val here = lookupRefBType(hostOwner.name)
        if(!allExceptionsAccessible(tcns, here)) {
          inlineTarget.warn(
            "Couldn't perform closure-inlining because not all exceptions " +
            "declared by the callee are accessible from the class containing the caller."
          )
          return null
        }

        // (5) Util.clone LocalVarNodes, shift as per-oracle
        val lvns: java.util.List[LocalVariableNode] = Util.clonedLocalVariableNodes(hiO, labelMap, "")
        val lvnIter = lvns.iterator()
        while(lvnIter.hasNext) {
          val lvn: LocalVariableNode = lvnIter.next()
          if(isInlinedLocalIdx(lvn.index)) {
            lvnIter.remove()
          } else {
            lvn.index = shiftedLocalIdx(lvn.index)
          }
        }
        if(!allLocalVarTypesAccessible(lvns, here)) {
          inlineTarget.warn(
            "Couldn't perform closure-inlining because not all LocalVariableNode types " +
            "declared by the callee are accessible from the class containing the caller."
          )
          return null
        }

        // (6) Shift LOADs and STOREs: (a) remove all isInlined LOADs; (b) shift as per oracle
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

        // (7) put together the pieces above into a MethodNode
        val shio: MethodNode =
          new MethodNode(
            Opcodes.ASM4,
            Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC | Opcodes.ACC_SYNTHETIC,
            name,
            shiOMethodType.getDescriptor,
            null,
            null
          )
        shio.instructions   = body
        shio.tryCatchBlocks = tcns
        shio.localVariables = lvns
        shio.maxStack  = hiO.maxStack // will be updated in due time (not before stubs have been pasted)
        shio.maxLocals = maxLocals

        // (8) rewrite usages (closure-apply invocations)
        //     For each usage obtain the stub (it's the same stub for all usages of the same closure), clone and paste.
        for(ccu <- closureClassUtils) {
          val stubsIter = getStubsIterator(ccu, shio)
          assert(ccu.closureUsages.usages.nonEmpty)
          for(usage0 <- ccu.closureUsages.usages) {
            val usage = insnMap.get(usage0)
            assert(body.contains(usage))
            assert(stubsIter.hasNext)
            body.insert(usage, stubsIter.next())
            body.remove(usage)
          }
          assert(!stubsIter.hasNext)
        }

        // (9) update maxStack
        Util.computeMaxLocalsMaxStack(shio)
        val quickOptimizer = new QuickCleanser(hostOwner)
        quickOptimizer.basicIntraMethodOpt(shio)
        Util.computeMaxLocalsMaxStack(shio)

        // (10) requireNonNull if needed, see SI-5850
        if(!hasNonNullReceiver && Util.isInstanceMethod(hiO)) {
          // similar in purpose to JDK7's j.u.Objects.requireNonNull
          val checkInsns = new InsnList
          checkInsns.add(new VarInsnNode(Opcodes.ALOAD, 0))
          val nonNullL  = new asm.Label
          val nonNullLN = new asm.tree.LabelNode(nonNullL)
          nonNullL.info = nonNullLN
          checkInsns.add(new JumpInsnNode(Opcodes.IFNONNULL, nonNullLN))
          checkInsns.add(new InsnNode(Opcodes.ACONST_NULL))
          checkInsns.add(new InsnNode(Opcodes.ATHROW))
          checkInsns.add(nonNullLN)
          shio.instructions.insert(checkInsns)
        }

        shio
      } // end of method buildStaticHiO()

      /**
       * `host` is patched to:
       *   (1) convey closure-constructor-args instead of an instantiated closure; and
       *   (2) target `staticHiO` rather than `hiO`
       *
       * How `host` looks before rewriting
       * ---------------------------------
       *
       * In terms of bytecode, two code sections are relevant:
       *   - instantiation of AC (the "Anonymous Closure"); and
       *   - passing it as argument to Hi-O:
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
       * How `host` looks after rewriting
       * --------------------------------
       *
       *   (a) The NEW, DUP, and < init > instructions for closure instantiation have been removed.
       *   (b) INVOKE Hi-O has been replaced by INVOKE shio,
       *       which expects on the operand stack not closures but their closure-state instead.
       *       The closure-state of a closure may consist of zero, one, or more arguments
       *       (usually an outer instance is part of the closure-state, but empty closure state is also possible).
       *
       * @param hostOwner class declaring the host method
       * @param host      method containing a callsite for which inlining has been requested
       * @param callsite  invocation of a higher-order method (taking one or more closures) whose inlining is requested
       * @param staticHiO a static method added to hostOwner, specializes hiO by inlining the closures hiO used to be invoked with
       *
       * @return whether closure-inlining was actually performed (should always be the case unless wrong input bytecode).
       */
      def rewriteHost(hostOwner:    ClassNode,
                      host:         MethodNode,
                      callsite:     MethodInsnNode,
                      staticHiO:    MethodNode,
                      inlineTarget: InlineTarget): Boolean = {

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
          inlineTarget.warn(
            "Couldn't perform closure-inlining because one or more closure instantiations couldn't be rewritten."
          )
          return false
        }

            def removeAll(ai: Array[_ <: AbstractInsnNode]) {
              ai foreach {i => host.instructions.remove(i) }
            }

        // This is the point of no return. Starting here, all closure-inlinings in `host` must succeed.

        removeAll(newInsns)
        removeAll(dupInsns)
        removeAll(initInsns)

        /*
         * No need to attempt eliding here those closure classes for which hostOwner is the only "master class".
         * Intra-class analysis `shakeAndMinimizeClosures()` will do that.
         * Actually, information on `nonMasterUsers` is complete by now
         * (because `populateNonMasterUsers()` runs before `inlining()`).
         * Thus in theory eliding could be done here. But that would add to the code to understand, unlike this comment, right? ;-)
         *
         * */

        val rewiredInvocation = new MethodInsnNode(Opcodes.INVOKESTATIC, hostOwner.name, staticHiO.name, staticHiO.desc)
        host.instructions.set(callsite, rewiredInvocation)
        Util.computeMaxLocalsMaxStack(host)

        true
      } // end of method rewriteHost()

      /**
       *  All of the usages of a closure in hiO are of the same shape: invocation of `applyMethod`
       *  whose receiver is LOAD of a closure-param.
       *
       *  The invoker of this method, `buildStaticHiO()`, will have an easier time if it just can replace
       *  those invocations without touching the instructions surrounding them.
       *
       *  To make that possible, this method returns copies (as many as closure usages) of a stub of instructions.
       *  The stub takes as starting point `stubTemplate` (a MethodNode where chains of apply-invocations
       *  have been collapsed into a self-contained method).
       *
       *  The stub is obtained by:
       *    (1) prefixing STORE instructions (whose locals are added here too) to consume the actual arguments
       *        the closure-usage used to consume.
       *    (2) reformulating GETFIELDs on closure-state, to use instead the spliced-in params in staticHiO
       *        (these params receive values that used to go to the closure's constructor)
       *    (3) properly shifting locals so that the resulting stub makes sense.
       */
      private def getStubsIterator(ccu: ClosureClassUtil, shio: MethodNode): Iterator[InsnList] = {

        val labelMap = Util.clonedLabels(ccu.stubTemplate)
        val stub = new InsnList

        val oldMaxLocals = shio.maxLocals
        val stores = new InsnList
        var accArgSizes = 0
        for(argT <- BType.getMethodType(ccu.stubTemplate.desc).getArgumentTypes) {
          val opcode = argT.getOpcode(Opcodes.ISTORE)
          stores.insert(new VarInsnNode(opcode, oldMaxLocals + accArgSizes))
          accArgSizes += argT.getSize
        }
        shio.maxLocals += ccu.stubTemplate.maxLocals

        val insnIter = ccu.stubTemplate.instructions.iterator()
        while(insnIter.hasNext) {
          val insn = insnIter.next()

          if(Util.isRETURN(insn)) {
            // elide
          } else if(insn.getType == AbstractInsnNode.VAR_INSN) {
            val vi = insn.asInstanceOf[VarInsnNode]
            if(vi.`var` == 0) {
              assert(vi.getOpcode == Opcodes.ALOAD)
              /*
               * case A: remove all `LOAD 0` instructions. THIS was to be consumed by a GETFIELD we'll also rewrite.
               */
            } else {
              /*
               * case B: rewrite LOADs for params of applyMethod.
               *         Past-maxLocals vars are fabricated (they are also used in the STOREs at the very beginning of the stub).
               *         Each `LOAD i` with 1 <= i is shifted
               */
              val updatedIdx = vi.`var` - 1 + oldMaxLocals
              assert(updatedIdx >= 0)
              val cloned = new VarInsnNode(vi.getOpcode, updatedIdx)
              stub.add(cloned)
            }
          } else if(
            (insn.getOpcode == Opcodes.GETFIELD) &&
            (insn.asInstanceOf[FieldInsnNode].owner == ccu.closureClass.name)
          ) {
            /*
             * case C: Given a GETFIELD in applyMethod, its localVarIdx in staticHiO is given by:
             *         shifted-localvaridx-of-closure-param + localvaridx-of-corresponding-constructor-param
             */
            val fa   = insn.asInstanceOf[FieldInsnNode]
            val base = shiftedLocalIdx(ccu.closureUsages.localVarIdxHiO)
            val dx   = ccu.stateField2constrParam(fa.name)
            val ft   = descrToBType(ccu.field(fa.name).desc)
            val opc  = ft.getOpcode(Opcodes.ILOAD)
            assert(base + dx >= 0)
            val load = new VarInsnNode(opc, base + dx)
            stub.add(load)
          } else {
            stub.add(insn.clone(labelMap))
          }

        }

        stub.insert(stores)

        var stubCopies: List[InsnList] = stub :: Nil
        for(i <- 2 to ccu.closureUsages.usages.size) {
          stubCopies ::=
            Util.clonedInsns(
              stub,
              Util.clonedLabels(stub),
              new java.util.HashMap[AbstractInsnNode, AbstractInsnNode]
            )
        }

        stubCopies.iterator
      } // end of method getStubsIterator()

    } // end of class StaticHiOUtil

  } // end of class WholeProgramAnalysis

} // end of class BCodeOptInter
