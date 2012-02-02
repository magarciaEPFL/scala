/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.nsc
package backend.icode.analysis

import scala.collection.{mutable, immutable}

/** A data-flow analysis on types, that works on `ICode`.
 *
 *  @author Iulian Dragos
 */
abstract class TypeFlowAnalysis {
  val global: Global
  import global._
  import definitions.{ ObjectClass, NothingClass, AnyRefClass, StringClass, ThrowableClass }

  /** The lattice of ICode types.
   */
  object typeLattice extends SemiLattice {
    type Elem = icodes.TypeKind

    val top    = icodes.REFERENCE(ObjectClass)
    val bottom = icodes.REFERENCE(NothingClass)

    def lub2(exceptional: Boolean)(a: Elem, b: Elem) =
      if (a eq bottom) b
      else if (b eq bottom) a
      else icodes.lub(a, b)
  }

  /** The lattice of type stacks. It is a straight forward extension of
   *  the type lattice (lub is pairwise lub of the list elements).
   */
  object typeStackLattice extends SemiLattice {
    import icodes._
    type Elem = TypeStack

    val top                   = new TypeStack
    val bottom                = new TypeStack
    val exceptionHandlerStack = new TypeStack(List(REFERENCE(AnyRefClass)))

    def lub2(exceptional: Boolean)(s1: TypeStack, s2: TypeStack) = {
      if (s1 eq bottom) s2
      else if (s2 eq bottom) s1
      else if ((s1 eq exceptionHandlerStack) || (s2 eq exceptionHandlerStack)) sys.error("merging with exhan stack")
      else {
//        if (s1.length != s2.length)
//          throw new CheckerException("Incompatible stacks: " + s1 + " and " + s2);
        new TypeStack((s1.types, s2.types).zipped map icodes.lub)
      }
    }
  }

  /** A map which returns the bottom type for unfound elements */
  class VarBinding extends mutable.HashMap[icodes.Local, icodes.TypeKind] {
    override def default(l: icodes.Local) = typeLattice.bottom

    def this(o: VarBinding) = {
      this()
      this ++= o
    }
  }

  /** The type flow lattice contains a binding from local variable
   *  names to types and a type stack.
   */
  object typeFlowLattice extends SemiLattice {
    import icodes._
    type Elem = IState[VarBinding, icodes.TypeStack]

    val top    = new Elem(new VarBinding, typeStackLattice.top)
    val bottom = new Elem(new VarBinding, typeStackLattice.bottom)

    def lub2(exceptional: Boolean)(a: Elem, b: Elem) = {
      val IState(env1, _) = a
      val IState(env2, _) = b

      val resultingLocals = new VarBinding
      env1 foreach { case (k, v) =>
        resultingLocals += ((k, typeLattice.lub2(exceptional)(v, env2(k))))
      }
      env2 collect { case (k, v) if resultingLocals(k) eq typeLattice.bottom =>
        resultingLocals += ((k, typeLattice.lub2(exceptional)(v, env1(k))))
      }
      val stack =
        if (exceptional) typeStackLattice.exceptionHandlerStack
        else typeStackLattice.lub2(exceptional)(a.stack, b.stack)

      IState(resultingLocals, stack)
    }
  }

  val timer = new Timer

  class MethodTFA extends DataFlowAnalysis[typeFlowLattice.type] {
    import icodes._
    import icodes.opcodes._

    type P = BasicBlock
    val lattice = typeFlowLattice

    val STRING = icodes.REFERENCE(StringClass)
    var method: IMethod = _

    /** Initialize the in/out maps for the analysis of the given method. */
    def init(m: icodes.IMethod) {
      this.method = m
      //typeFlowLattice.lubs = 0
      init {
        worklist += m.startBlock
        worklist ++= (m.exh map (_.startBlock))
        m foreachBlock { b =>
          in(b)  = typeFlowLattice.bottom
          out(b) = typeFlowLattice.bottom
        }

        // start block has var bindings for each of its parameters
        val entryBindings     = new VarBinding ++= (m.params map (p => ((p, p.kind))))
        in(m.startBlock) = lattice.IState(entryBindings, typeStackLattice.bottom)

        m.exh foreach { e =>
          in(e.startBlock) = lattice.IState(in(e.startBlock).vars, typeStackLattice.exceptionHandlerStack)
        }
      }
    }

    def this(m: icodes.IMethod) {
      this()
      init(m)
    }

    def run = {
      timer.start
      // icodes.lubs0 = 0
      forwardAnalysis(blockTransfer)
      val t = timer.stop
      if (settings.debug.value) {
        linearizer.linearize(method).foreach(b => if (b != method.startBlock)
          assert(visited.contains(b),
            "Block " + b + " in " + this.method + " has input equal to bottom -- not visited? .." + visited));
      }
      // log("" + method.symbol.fullName + " ["  + method.code.blocks.size + " blocks] "
      //     + "\n\t" + iterations + " iterations: " + t + " ms."
      //     + "\n\tlubs: " + typeFlowLattice.lubs + " out of which " + icodes.lubs0 + " typer lubs")
    }

    def blockTransfer(b: BasicBlock, in: lattice.Elem): lattice.Elem = {
      var result = lattice.IState(new VarBinding(in.vars), new TypeStack(in.stack))
      var instrs = b.toList
      while(!instrs.isEmpty) {
        val i  = instrs.head
        result = mutatingInterpret(result, i)
        instrs = instrs.tail
      }
      result
    }

    /** Abstract interpretation for one instruction. */
    def interpret(in: typeFlowLattice.Elem, i: Instruction): typeFlowLattice.Elem = {
      val out = lattice.IState(new VarBinding(in.vars), new TypeStack(in.stack))
      mutatingInterpret(out, i)
    }

    def mutatingInterpret(out: typeFlowLattice.Elem, i: Instruction): typeFlowLattice.Elem = {
      val bindings = out.vars
      val stack = out.stack

      if (settings.debug.value) {
        // Console.println("[before] Stack: " + stack);
        // Console.println(i);
      }
      i match {

        case THIS(clasz) =>
          stack push toTypeKind(clasz.tpe)

        case CONSTANT(const) =>
          stack push toTypeKind(const.tpe)

        case LOAD_ARRAY_ITEM(kind) =>
          stack.pop2 match {
            case (idxKind, ARRAY(elem)) =>
              assert(idxKind == INT || idxKind == CHAR || idxKind == SHORT || idxKind == BYTE)
              stack.push(elem)
            case (_, _) =>
              stack.push(kind)
          }

        case LOAD_LOCAL(local) =>
          val t = bindings(local)
          stack push (if (t == typeLattice.bottom) local.kind  else t)

        case LOAD_FIELD(field, isStatic) =>
          if (!isStatic)
            stack.pop
          stack push toTypeKind(field.tpe)

        case LOAD_MODULE(module) =>
          stack push toTypeKind(module.tpe)

        case STORE_ARRAY_ITEM(kind) =>
          stack.pop3

        case STORE_LOCAL(local) =>
          val t = stack.pop
          bindings += (local -> t)

        case STORE_THIS(_) =>
          stack.pop

        case STORE_FIELD(field, isStatic) =>
          if (isStatic)
            stack.pop
          else
            stack.pop2

        case CALL_PRIMITIVE(primitive) =>
          primitive match {
            case Negation(kind) =>
              stack.pop; stack.push(kind)
            case Test(_, kind, zero) =>
              stack.pop
              if (!zero) stack.pop
              stack push BOOL;
            case Comparison(_, _) =>
              stack.pop2
              stack push INT

            case Arithmetic(op, kind) =>
              stack.pop
              if (op != NOT)
                stack.pop
              val k = kind match {
                case BYTE | SHORT | CHAR => INT
                case _ => kind
              }
              stack push k

            case Logical(op, kind) =>
              stack.pop2
              stack push kind

            case Shift(op, kind) =>
              stack.pop2
              stack push kind

            case Conversion(src, dst) =>
              stack.pop
              stack push dst

            case ArrayLength(kind) =>
              stack.pop
              stack push INT

            case StartConcat =>
              stack.push(ConcatClass)

            case EndConcat =>
              stack.pop
              stack.push(STRING)

            case StringConcat(el) =>
              stack.pop2
              stack push ConcatClass
          }

        case cm @ CALL_METHOD(_, _) =>
          stack pop cm.consumed
          cm.producedTypes foreach (stack push _)

        case BOX(kind) =>
          stack.pop
          stack.push(BOXED(kind))

        case UNBOX(kind) =>
          stack.pop
          stack.push(kind)

        case NEW(kind) =>
          stack.push(kind)

        case CREATE_ARRAY(elem, dims) =>
          stack.pop(dims)
          stack.push(ARRAY(elem))

        case IS_INSTANCE(tpe) =>
          stack.pop
          stack.push(BOOL)

        case CHECK_CAST(tpe) =>
          stack.pop
          stack.push(tpe)

        case SWITCH(tags, labels) =>
          stack.pop

        case JUMP(whereto) =>
          ()

        case CJUMP(success, failure, cond, kind) =>
          stack.pop2

        case CZJUMP(success, failure, cond, kind) =>
          stack.pop

        case RETURN(kind) =>
          if (kind != UNIT)
            stack.pop;

        case THROW(_) =>
          stack.pop

        case DROP(kind) =>
          stack.pop

        case DUP(kind) =>
          stack.push(stack.head)

        case MONITOR_ENTER() =>
          stack.pop

        case MONITOR_EXIT() =>
          stack.pop

        case SCOPE_ENTER(_) | SCOPE_EXIT(_) =>
          ()

        case LOAD_EXCEPTION(clasz) =>
          stack.pop(stack.length)
          stack.push(toTypeKind(clasz.tpe))

        case _ =>
          dumpClassesAndAbort("Unknown instruction: " + i)
      }
      out
    } // interpret


    class SimulatedStack {
      private var types: List[InferredType] = Nil
      private var depth = 0

      /** Remove and return the topmost element on the stack. If the
       *  stack is empty, return a reference to a negative index on the
       *  stack, meaning it refers to elements pushed by a predecessor block.
       */
      def pop: InferredType = types match {
        case head :: rest =>
          types = rest
          head
        case _ =>
          depth -= 1
          TypeOfStackPos(depth)
      }

      def pop2: (InferredType, InferredType) = {
        (pop, pop)
      }

      def push(t: InferredType) {
        depth += 1
        types = types ::: List(t)
      }

      def push(k: TypeKind) { push(Const(k)) }
    }

	abstract class InferredType {
      /** Return the type kind pointed by this inferred type. */
      def getKind(in: lattice.Elem): icodes.TypeKind = this match {
        case Const(k) =>
          k
        case TypeOfVar(l: icodes.Local) =>
          if (in.vars.isDefinedAt(l)) in.vars(l) else l.kind
        case TypeOfStackPos(n: Int) =>
          assert(in.stack.length >= n)
          in.stack(n)
      }
    }
	/** A type that does not depend on input to the transfer function. */
	case class Const(t: icodes.TypeKind) extends InferredType
	/** The type of a given local variable. */
	case class TypeOfVar(l: icodes.Local) extends InferredType
	/** The type found at a stack position. */
	case class TypeOfStackPos(n: Int) extends InferredType

	abstract class Gen
	case class Bind(l: icodes.Local, t: InferredType) extends Gen
	case class Push(t: InferredType) extends Gen

    /** A flow transfer function of a basic block. */
	class TransferFunction(consumed: Int, gens: List[Gen]) extends (lattice.Elem => lattice.Elem) {
	  def apply(in: lattice.Elem): lattice.Elem = {
        val out = lattice.IState(new VarBinding(in.vars), new TypeStack(in.stack))
        val bindings = out.vars
        val stack = out.stack

        out.stack.pop(consumed)
        for (g <- gens) g match {
          case Bind(l, t) =>
            out.vars += (l -> t.getKind(in))
          case Push(t) =>
            stack.push(t.getKind(in))
        }
        out
      }
	}
  }

  case class CallsiteInfo(bb: icodes.BasicBlock, receiver: Symbol, stackLength: Int, concreteMethod: Symbol)

  case class TypeFlowInfo(receiver: Symbol, stackLength: Int, concreteMethod: Symbol)

  /*

    Usually, a type-flow analysis on a method computes in- and out-flows for each basic block in the method.
    For the purposes of Inliner, that's enough to make sure that by the time a inlining candidate (a CALL_METHOD instruction) is visited its abstracted type-stack-slot is known.
    This subclass (MTFAGrowable) of MethodTFA also aims at performing such analysis on CALL_METHOD instructions, with a difference:

      (a) an early screening is performed while the type-flow is being computed (in an override of `blockTransfer`) testing a subset of the conditions that must be checked later.
          The reasoning here is: if the early check fails at some iteration, there's no chance a follow-up iteration (with a yet more lub-ed type-stack-slot) will succeed.
          Failure is sufficient to remove that particular CALL_METHOD from the typeflow's `remainingCALLs`.

      (b) in case the early check does not fail, no conclusive decision can be made, so everything goes on as in the standard version.

    In other words, `remainingCALLs` tracks at any time those callsites that still remain as candidates for inlining
    (the map also caches info about the receiver so as to spare computing it again in case inlining does occur).

    Besides caching, a further optimization involves skipping visiting those basic blocks whose in-flow and out-flow isn't needed anway (as explained next).
    A basic block lacking a callsite in `remainingCALLs`, when visisted by the standard algorithm, will not result in any inlining.
    But as we know from the way a type-flow is computed, computing the in- and out-flow for a basic block relies on those of other basic blocks.
    How to keep those, while discarding the rest?

    In detail, we want to focus on that sub-graph of the CFG such that control flow may reach a remaining candidate callsite.
    Those basic blocks not in that subgraph can be skipped altogether (that's why `forwardAnalysis()` in `MTFAGrowable` now checks for inclusion of a basic block in `relevantBBs`
    before adding the block to the worklist, and as part of choosing successors).
    The bookkeeping supporting on-the-fly pruning of irrelevant blocks requires overridding most methods of the dataflow-analysis.

    The rest of the story takes place in Inliner, which does not visit all of the method's basic blocks but only on those represented in `remainingCALLs`.

   */
  class MTFAGrowable extends MethodTFA {

    import icodes._

    val remainingCALLs = mutable.Map.empty[opcodes.CALL_METHOD, CallsiteInfo]

    val preCandidates  = mutable.Map.empty[BasicBlock, List[opcodes.CALL_METHOD]]
    val trackedRCVR    = mutable.Map.empty[opcodes.CALL_METHOD, TypeFlowInfo]

    override def run {
      super.run
      // prepare two maps (`preCandidates` and `trackedRCVR`) for use by Inliner by reshuffling the contents of `remainingCALLs`
      preCandidates.clear()
      trackedRCVR.clear()
      for(rc <- remainingCALLs) {
        val Pair(cm, CallsiteInfo(bb, receiver, stackLength, concreteMethod)) = rc
        val preCands = preCandidates.getOrElse(bb, Nil)
        preCandidates += (bb -> (cm :: preCands))
        trackedRCVR   += (cm -> TypeFlowInfo(receiver, stackLength, concreteMethod))
      }
      for(pc <- preCandidates) {
        val Pair(bb, unsortedPreCands) = pc
        val sortedPreCands = (bb.toList filter { i => unsortedPreCands contains i }).asInstanceOf[List[opcodes.CALL_METHOD]]
        preCandidates += (bb -> sortedPreCands)
        assert(sortedPreCands.nonEmpty)
      }
    }

    override def blockTransfer(b: BasicBlock, in: lattice.Elem): lattice.Elem = {
      var result = lattice.IState(new VarBinding(in.vars), new TypeStack(in.stack))
      var shrinkedWatchlist = false
      var instrs = b.toList
      while(!instrs.isEmpty) {
        val i  = instrs.head

        if(isOnWatchlist(i)) {
          val cm = i.asInstanceOf[opcodes.CALL_METHOD]
          val msym = cm.method
          val paramsLength = msym.info.paramTypes.size
          val receiver = result.stack.types.drop(paramsLength).head match {
            case REFERENCE(s) => s
            case _            => NoSymbol // e.g. BOX(s)
          }
          val concreteMethod = inliner.lookupImplFor(msym, receiver)
          val isCandidate = ( inliner.isClosureClass(receiver) || concreteMethod.isEffectivelyFinal || receiver.isEffectivelyFinal )
          if(isCandidate) {
            remainingCALLs += Pair(cm, CallsiteInfo(b, receiver, result.stack.length, concreteMethod))
          } else {
            remainingCALLs.remove(cm)
            isOnWatchlist.remove(cm)
            shrinkedWatchlist = true
          }
        }

        result = mutatingInterpret(result, i)
        instrs = instrs.tail
      }

      if(shrinkedWatchlist) {
        val isWatching = (b.toList exists isOnWatchlist)
        if(!isWatching) {
          val watchers = relevantBBs.toSet filter { x => x.toList exists isOnWatchlist }
          val updated  = transitivePreds(watchers)
          relevantBBs.clear()
          relevantBBs ++= updated
        }
      }

      result
    }

    val isOnWatchlist = mutable.Set.empty[Instruction]

    // those basic blocks with a pre-candidate (as well as all of their predecessors) will be visited by the TFA, the rest will be skipped.
    val relevantBBs   = mutable.Set.empty[BasicBlock]

    private def isPreCandidate(i: Instruction): Boolean = {
      if(!i.isInstanceOf[opcodes.CALL_METHOD]) { return false }
      val cm = i.asInstanceOf[opcodes.CALL_METHOD]
      val msym  = cm.method
      val style = cm.style
      // Dynamic == normal invocations
      // Static(true) == calls to private members
      !msym.isConstructor && (style.isDynamic || (style.hasInstance && style.isStatic))
      // && !(msym hasAnnotation definitions.ScalaNoInlineClass)
    }

    override def init(m: icodes.IMethod) {
      super.init(m)
      remainingCALLs.clear()
      // initially populate the watchlist with any callsite that stands a chance of being inlined
      isOnWatchlist.clear()
      val bbsWithPreCands = putOnRadar(m.blocks)
      relevantBBs.clear()
      relevantBBs ++= transitivePreds(bbsWithPreCands)
      assert(relevantBBs.isEmpty || relevantBBs.contains(m.startBlock), "you gave me dead code")
    }

    private def putOnRadar(blocks: Traversable[BasicBlock]): List[BasicBlock] = {
      var bbsWithPreCands: List[BasicBlock] = Nil
      for(bb <- blocks; val preCands = bb.toList filter isPreCandidate; if preCands.nonEmpty) {
        bbsWithPreCands = bb :: bbsWithPreCands
        isOnWatchlist ++= preCands
      }
      bbsWithPreCands
    }

    /* those BBs in the argument are also included in the result */
    private def transitivePreds(starters: Traversable[BasicBlock]): Set[BasicBlock] = {
      val result = mutable.Set.empty[BasicBlock]
      var toVisit: List[BasicBlock] = starters.toList.distinct
      while(toVisit.nonEmpty) {
        val h   = toVisit.head
        toVisit = toVisit.tail
        result += h
        for(p <- h.predecessors; if !result(p) && !toVisit.contains(p)) { toVisit = p :: toVisit }
      }
      result.toSet
    }

    /* those BBs in the argument are also included in the result */
    private def transitiveSuccs(starters: Traversable[BasicBlock]): Set[BasicBlock] = {
      val result = mutable.Set.empty[BasicBlock]
      var toVisit: List[BasicBlock] = starters.toList.distinct
      while(toVisit.nonEmpty) {
        val h   = toVisit.head
        toVisit = toVisit.tail
        result += h
        for(p <- h.successors; if !result(p) && !toVisit.contains(p)) { toVisit = p :: toVisit }
      }
      result.toSet
    }






    /** discards what must be discarded, blanks what needs to be blanked out, and keeps the rest. */
    def reinit(m: icodes.IMethod, staleOut: List[BasicBlock], inlined: collection.Set[BasicBlock], staleIn: collection.Set[BasicBlock]) {
      if (this.method == null || this.method.symbol != m.symbol) {
        init(m)
        return
      } else if(staleOut.isEmpty && inlined.isEmpty && staleIn.isEmpty) {
        // this promotes invoking reinit if in doubt, no performance degradation will ensue!
        return;
      }

      reinit {
        // asserts conveying an idea what CFG shapes arrive here.
        // staleIn foreach (p => assert( !in.isDefinedAt(p), p))
        // staleIn foreach (p => assert(!out.isDefinedAt(p), p))
        // inlined foreach (p => assert( !in.isDefinedAt(p), p))
        // inlined foreach (p => assert(!out.isDefinedAt(p), p))
        // inlined foreach (p => assert(!p.successors.isEmpty || p.lastInstruction.isInstanceOf[icodes.opcodes.THROW], p))
        // staleOut foreach (p => assert(  in.isDefinedAt(p), p))

        // never rewrite in(m.startBlock)
        staleOut foreach { b =>
          if(!inlined.contains(b)) { worklist += b }
          out(b)    = typeFlowLattice.bottom
        }
        // nothing else is added to the worklist, bb's reachable via succs will be tfa'ed
        blankOut(inlined)
        blankOut(staleIn)
        // no need to add startBlocks from m.exh
      }

      /* those instructions originally following the inlined callsite (but in the same basic block)
       * are now contained in the afterBlock created to that effect. Each block in staleIn is one such `afterBlock`. */
      for(afterBlock <- staleIn) {
        val justCALLsAfter = afterBlock.toList collect { case c : opcodes.CALL_METHOD => c }
        for(ia <- justCALLsAfter; if remainingCALLs.isDefinedAt(ia)) {
          val updValue = remainingCALLs(ia).copy(bb = afterBlock)
          remainingCALLs += Pair(ia, updValue)
        }
      }

      // don't forget watching those new precandidates
      val shadow = transitiveSuccs(inlined ++ staleIn)
      val bbsWithPreCands = putOnRadar(shadow)
      val feeders = transitivePreds(bbsWithPreCands)
      relevantBBs ++= staleOut
      relevantBBs ++= (feeders intersect shadow)

     } // end of method reinit

    private def blankOut(blocks: collection.Set[BasicBlock]) {
      blocks foreach { b =>
        in(b)     = typeFlowLattice.bottom
        out(b)    = typeFlowLattice.bottom
      }
    }

    override def forwardAnalysis(f: (P, lattice.Elem) => lattice.Elem): Unit = {
      while (!worklist.isEmpty && relevantBBs.nonEmpty) {
        if (stat) iterations += 1
        val point = worklist.iterator.next; worklist -= point; visited += point;
        if(relevantBBs(point)) {
          val output = f(point, in(point))
          if ((lattice.bottom == out(point)) || output != out(point)) {
            out(point) = output
            val succs = point.successors filter relevantBBs
            succs foreach { p =>
              val updated = lattice.lub(in(p) :: (p.predecessors map out.apply), p.exceptionHandlerStart)
              if(updated != in(p)) {
                in(p) = updated
                if (!worklist(p)) { worklist += p; }
              }
            }
          }
        }
      }
    }

  }

  class Timer {
    var millis = 0L

    private var lastStart = 0L

    def reset() {
      millis = 0L
    }

    def start() {
      lastStart = System.currentTimeMillis
    }

    /** Stop the timer and return the number of milliseconds since the last
     * call to start. The 'millis' field is increased by the elapsed time.
     */
    def stop: Long = {
      val elapsed = System.currentTimeMillis - lastStart
      millis += elapsed
      elapsed
    }
  }
}
