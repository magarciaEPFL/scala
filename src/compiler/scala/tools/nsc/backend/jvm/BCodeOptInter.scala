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
import asm.tree._

import scala.collection.{ mutable, immutable }
import scala.Some

/*
 *  Optimize and tidy-up bytecode before it's serialized for good.
 *  This class focuses on inter-procedural optimizations.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOptInter extends BCodeTFA {

  import global._

  val knownLacksInline = mutable.Set.empty[Symbol] // cache to avoid multiple inliner.hasInline() calls.
  val knownHasInline   = mutable.Set.empty[Symbol] // as above. Motivated by the need to warn on "inliner failures".

  final def hasInline(sym: Symbol) = {
    if      (knownLacksInline(sym)) false
    else if (knownHasInline(sym))   true
    else {
      val b = (sym hasAnnotation definitions.ScalaInlineClass)
      if (b) { knownHasInline   += sym }
      else   { knownLacksInline += sym }

      b
    }
  }

  final def hasNoInline(sym: Symbol) = sym hasAnnotation definitions.ScalaNoInlineClass

  /* must-single-thread */
  def clearBCodeOpt() {
    cgns.clear()
    codeRepo.clear()
    closuRepo.clear()
    knownLacksInline.clear()
    knownHasInline.clear()
    elidedClasses.clear()
    clearBCodeTypes()
  }

  //--------------------------------------------------------
  // Optimization pack: Method-inlining and Closure-inlining
  //--------------------------------------------------------

  val cgns = new mutable.PriorityQueue[CallGraphNode]()(cgnOrdering)

  /*
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
  final class CallGraphNode(val hostOwner: asm.tree.ClassNode, val host: asm.tree.MethodNode) {

    var hiOs:  List[InlineTarget] = Nil
    var procs: List[InlineTarget] = Nil

    def isEmpty    = (hiOs.isEmpty && procs.isEmpty)
    def candidates = (hiOs ::: procs).sorted(inlineTargetOrdering)

    def directCallees: Set[asm.tree.MethodNode] = {
      hiOs.map(_.callee).toSet ++ procs.map(_.callee)
    }

    /*
     * Initially the invocation instructions (one for each InlineTarget)
     * haven't been resolved to the MethodNodes they target.
     * This method takes care of that, setting `InlineTarget.callee` and `InlineTarget.owner` as a side-effect.
     *
     * can-multi-thread, provided each callsite.owner has been entered as TypeName in Names.
     */
    def populate() {
      if (!asm.optimiz.Util.isReadyForAnalyzer(host)) {
        asm.optimiz.Util.computeMaxLocalsMaxStack(host)
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
      var result = x.hostOwner.name.compare(y.hostOwner.name)
      if (result == 0) {
        val a = (x.host.name + x.host.desc)
        val b = (y.host.name + y.host.desc)
        result = a compare b
      }
      result
    }
  }

  /*
   *  An inlining request, given by a callsite and items for error reporting.
   *
   *  @param callsite for which inlining has been requested
   *  @param cunit    for error reporting
   *  @param pos      for error reporting
   *
   */
  final class InlineTarget(val callsite: asm.tree.MethodInsnNode, val cunit: CompilationUnit, val pos: Position) {

    var callee: asm.tree.MethodNode = null // the concrete callee denoted by the callsite
    var owner:  asm.tree.ClassNode  = null // the class declaring the callee

    def populate() {
      val ownerBT = lookupRefBType(callsite.owner)
      // `null` usually indicates classfile wasn't found and thus couldn't be parsed. TODO warning?
      val mnAndOwner = codeRepo.getMethodOrNull(ownerBT, callsite.name, callsite.desc)
      if (mnAndOwner != null) {
        callee = mnAndOwner.mnode
        owner  = mnAndOwner.owner
        if (!asm.optimiz.Util.isReadyForAnalyzer(callee)) {
          asm.optimiz.Util.computeMaxLocalsMaxStack(callee)
        }
      }
    }

    def calleeId: String = { owner.name + "::" + callee.name + callee.desc }

    def warn(msg: String) {
      if (!settings.YinlinerWarnings) {
        // otherwise partest prints out a summary message "there were N inliner warning(s); re-run with -Yinline-warnings for details"
        // and the ensuing "[output differs]" (-neo:GenASM emits none of those warnings)
        return
      }
      cunit.inlinerWarning(pos, msg)
    }

    /* is the target of the callsite part of the program being compiled? */
    def isBeingCompiled: Boolean = {
      val ownerBT = lookupRefBType(callsite.owner)
      codeRepo.classes.containsKey(ownerBT)
    }

  }

  object inlineTargetOrdering extends scala.math.Ordering[InlineTarget] {
    def compare(x: InlineTarget, y: InlineTarget): Int = {
      x.hashCode().compare(y.hashCode())
    }
  }

  abstract class WholeProgramOptMethodInlining {

    import asm.tree.analysis.{Analyzer, BasicValue, BasicInterpreter}

    val unreachCodeRemover = new asm.optimiz.UnreachableCode

    def inlineClosures(hostOwner:          ClassNode,
                       host:               MethodNode,
                       callsiteTypeFlow:   asm.tree.analysis.Frame[TFValue],
                       inlineTarget:       InlineTarget,
                       hasNonNullReceiver: Boolean): Option[String]

    /*
     *  TODO documentation
     *
     *  must-single-thread due to `inlining()`
     *
     */
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

    /*
     * shio methods are collected as they are built in the `privatizables` map, grouped by their ownning class.
     * (That class also owns what used to be the endpoint of the delegating-closure that was inlined).
     *
     * shio methods spend most of their time as public methods, so as not to block method-inlining
     * (they're synthetically generated, thus it would come as a surprise if they required attention from the developer).
     * However, in case no method-inlining transplanted them to another class, they are made private as initially intended.
     */
    val privatizables = new MethodsPerClass

    class MethodsPerClass extends mutable.HashMap[BType, List[MethodNode]] {

      def track(k: ClassNode, v: MethodNode) { track(lookupRefBType(k.name), v) }
      def track(k: BType,     v: MethodNode) { put(k, v :: getOrElse(k, Nil)) }

      /*
       *  It's ok trying to untrack a method that's not being tracked. If in doubt, call untrack()
       */
      def untrack(k: BType, v: MethodNode) {
        val v2 = getOrElse(k, Nil) filterNot { _ eq v }
        if (v2.isEmpty) { remove(k)  }
        else            { put(k, v2) }
      }

      /*
       *  It's ok trying to untrack a method that's not being tracked. If in doubt, call untrack()
       */
      def untrack(k: BType, methodName: String, methodDescr: String) {
        val v2 = getOrElse(k, Nil) filterNot { mn => (mn.name == methodName) && (mn.desc == methodDescr) }
        if (v2.isEmpty) { remove(k)  }
        else            { put(k, v2) }
      }

    } // end of class MethodsPerClass

    // -------------------------------------------------------------------------------
    // ------------------------------- inlining rounds -------------------------------
    // -------------------------------------------------------------------------------

    /*
     *  Performs closure-inlining and method-inlining, by first breaking any cycles
     *  over the "inlined-into" relation (see local method `isReachable()`).
     *  Afterwards,
     *    - `WholeProgramAnalysis.inlineMethod()`   takes care of method-inlining
     *    - `WholeProgramAnalysis.inlineClosures()` of closure-inlining
     *
     *  must-single-thread
     *
     */
    private def inlining() {

      isInliningDone = true

      // without committing to compile-time-libraries also being used at runtime,
      // the only inlinings we can perform are those where callee is being compiled.
      if (!settings.isCrossLibOpt) {
        for(cgn <- cgns) {
          cgn.hiOs  = cgn.hiOs  filter { it: InlineTarget => it.isBeingCompiled }
          cgn.procs = cgn.procs filter { it: InlineTarget => it.isBeingCompiled }
        }
      }

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

      /*
       * @return true iff there's a chain of inline-requests starting at `start` that contains `goal`
       */
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

      /*
       *  It only remains to visit the elements of `cgns` in an order that ensures
       *  a CallGraphNode has stabilitzed by the time it's inlined into a host method.
       *  "A CallGraphNode has stabilized" means all inlinings have been performed inside it,
       *  where those inlinings were based on callees that were themselves already stabilized.
       */
      val remaining = mutable.Set.empty[CallGraphNode]
      remaining ++= cgns.toList
      while (remaining.nonEmpty) {
        val leaves = remaining.filter( cgn => cgn.candidates.forall( c => !mn2cgn.contains(c.callee) || !remaining.contains(mn2cgn(c.callee)) ) )
        assert(leaves.nonEmpty, "Otherwise loop forever")
        inliningRound(leaves)
        remaining --= leaves
      }

    } // end of method inlining()

    /*
     *  TODO use task-parallelism (inlining is the bottleneck, with bytecode parsing perhaps a large contributor).
     *  In more detail:
     *    (a) all `leaves` sharing the same `hostOwner` should be inlined in a fixed sequence (for test.stability purposes).
     *    (b) after partitioning `leaves` by `hostOwner` different partitions can be processed in parallel.
     *
     *  @param leaves set of inlining requests that are independent from each other.
     *
     */
    private def inliningRound(leaves: collection.Set[CallGraphNode]) {

      leaves.toList.sorted(cgnOrdering).foreach { leaf => inlineCallees(leaf) }

    }

    /*
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

      severalMethodInlinings(leaf, tfaFrameAt)

      //------------------------------
      // Part 4 of 4: closure-inlining
      //------------------------------

      severalClosureInlinings(leaf, tfaFrameAt)

      ifDebug {
        val da = new Analyzer[BasicValue](new asm.tree.analysis.BasicVerifier)
        da.analyze(leaf.hostOwner.name, leaf.host)
      }

    } // end of method inlineCallees()

    private def severalMethodInlinings(leaf:       CallGraphNode,
                                       tfaFrameAt: Map[MethodInsnNode, asm.tree.analysis.Frame[TFValue]]) {

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
          isDefinitelyNonNull   = isRcvNonNull,
          skipCalleeLineNumbers = !codeRepo.isDebugInfoConsistent(leaf.hostOwner, proc.owner)
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

    }

    def severalClosureInlinings(leaf:       CallGraphNode,
                                tfaFrameAt: Map[MethodInsnNode, asm.tree.analysis.Frame[TFValue]])

    /*
     * SI-5850: Inlined code shouldn't forget null-check on the original receiver
     */
    def isReceiverKnownNonNull(frame: asm.tree.analysis.Frame[TFValue], callsite: MethodInsnNode): Boolean = {
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

    /*
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
                     isDefinitelyNonNull:   Boolean,
                     skipCalleeLineNumbers: Boolean): Option[String] = {

      assert(callee != null)
      assert(callsite.name == callee.name)
      assert(callsite.desc == callee.desc)
      assert(!Util.isConstructor(callee))

      if (!host.instructions.contains(callsite)) {
        val diagnostics =
           "That's strange. A callsite that was going to be inlined has been marked as dead-code. " +
          s"Callsite: ${insnPos(callsite, host)} , in method ${methodSignature(hostOwner, host)}"
        return Some(diagnostics)
      }

      /*
       * Situation (a.0) under which method-inlining is unfeasible: synchronized callee.
       */
      if (Util.isSynchronizedMethod(callee)) {
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
      if (!callee.tryCatchBlocks.isEmpty) {
        val stackHeight       = frame.getStackSize
        val expectedArgs: Int = Util.expectedArgs(callsite)
        if (stackHeight > expectedArgs) {
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
      if (skipCalleeLineNumbers) {
        codeRepo.removeLineNumberNodes(body)
      }
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
      codeRepo.registerUnseenTypeNames(callee) // must-single-thread

      val hostOwnerBT = lookupRefBType(hostOwner)

      val illegalAccessInsn = allAccessesLegal(body, hostOwnerBT)
      if (illegalAccessInsn != null) {
        return Some(
          s"Callee ${methodSignature(calleeOwner, callee)} contains instruction \n${Util.textify(illegalAccessInsn)} " +
          s"that would cause IllegalAccessError from class $hostOwner"
        )
      }

      val calleeMethodType = BType.getMethodType(callee.desc) // must-single-thread

      /*
       * Situation (a.3) under which method-inlining is unfeasible: callee has Nothing type.
       */
      if (calleeMethodType.getReturnType.isNothingType) {
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
      if (Util.isInstanceMethod(callee)) {
        if (!isDefinitelyNonNull) {
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

      /*
       * body may contain xRETURN instructions, each should be replaced at that program point
       * by DROPs (as needed) for all slots but stack-top.
       */
      def replaceRETURNs() {
        val retType        = calleeMethodType.getReturnType
        val hasReturnValue = !retType.isUnitType
        val retVarIdx      = host.maxLocals + callee.maxLocals
        nxtLocalIdx       += retType.getSize

        if (hasReturnValue) {
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
          if (hasReturnValue)  { retRepl.add(retVarStore(retInsn)) }
          else if (height > 0) { retRepl.add(Util.getDrop(frame.peekDown(0).getSize)) }
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

      checkTransplantedAccesses(body, hostOwnerBT)

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

    def logInlining(success:   Boolean,
                    hostOwner: String,
                    host:      MethodNode,
                    callsite:  MethodInsnNode,
                    isHiO:     Boolean,
                    isReceiverKnownNonNull: Boolean,
                    hiO:       MethodNode,
                    hiOOwner:  ClassNode) {

      val kind    = if (isHiO)   "closure-inlining "  else "method-inlining "
      val leading = if (success) "Successful " + kind else "Failed " + kind

      log(leading + s"Callsite: ${Util.textify(callsite)} , in method ${methodSignature(hostOwner, host)}")

      if (!success) {
        debuglog(s"Bytecode of callee, declared by ${hiOOwner.name} \n${Util.textify(hiO)}")
      }

    } // end of method logInlining()

    /*
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
    def allAccessesLegal(body: InsnList, here: BType): AbstractInsnNode = {

      /*
       * @return whether the first argument is a subtype of the second, or both are the same BType.
       */
      def isSubtypeOrSame(a: BType, b: BType): Boolean = {
        (a == b) || {
          val ax = exemplars.get(a)
          val bx = exemplars.get(b)

          (ax != null) && (bx != null) && ax.isSubtypeOf(b)
        }
      }

      /*
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
      while (iter.hasNext) {
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
            if (et.hasObjectSort) isAccessible(et, here)
            else true

          case _ => true
        }
        if (!isLegal) {
          return insn
        }
      }

      null // stands for "all accesses legal"

    } // end of method allAccessesLegal()

    /*
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
    def isAccessible(there: BType, here: BType): Boolean = {
      if (!there.isNonSpecial) true
      else if (there.isArray) isAccessible(there.getElementType, here)
      else {
        assert(there.hasObjectSort, s"not of object sort: ${there.getDescriptor}")
        (there.getRuntimePackage == here.getRuntimePackage) || exemplars.get(there).isPublic
      }
    }

    def checkTransplantedAccesses(body: InsnList, enclClass: BType) {

      /*
       * An invocation to a shio method declared in a class other than the new home of the callsite (enclClass)
       * forces the shio method in question to remain public.
       */
      body foreachInsn { insn =>
        insn match {
          case mi: MethodInsnNode =>
            val calleeOwnerBT = lookupRefBType(mi.owner)
            if (calleeOwnerBT != enclClass) {
              // it's ok to try to untrack a method that's not being tracked
              privatizables.untrack(calleeOwnerBT, mi.name, mi.desc)
            }
          case _ => ()
        }
      }

      /*
       * In case `insn` denotes a dclosure instantiation or endpoint invocation
       * and `enclClass` isn't the master class of that dclosure, note this fact `nonMasterUsers`.
       */
      body foreachInsn { insn => closuRepo.trackClosureUsageIfAny(insn, enclClass) }

    }

  } // end of class WholeProgramAnalysis

} // end of class BCodeOptInter
