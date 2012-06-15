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

  }

  val bottomXTK = XTK(typeLattice.bottom)

  /* TypeKind extended with flags for type-exactness and non-nullness. */
  final class XTK private (val tk: icodes.TypeKind, val isExact: Boolean, val isNonNull: Boolean) {
    assert((bottomXTK == null)        ||
           (tk != typeLattice.bottom) ||
           isBottom, "there can be only one bottomXTK, one has been found even after bottomXTK has been initialized.")

    @inline def isBottom = (this eq bottomXTK)

    override def equals(that: Any) = {
      that match {
        case XTK(t, e, n) => (t == tk) && (e == isExact) && (n == isNonNull)
        case _            => false
      }
    }
    override def hashCode = (tk.hashCode)

  }
  object XTK {
    def apply(tk: icodes.TypeKind, isExact: Boolean, isNonNull: Boolean): XTK = {
      if(tk == typeLattice.bottom) {
        if(bottomXTK == null) new XTK(typeLattice.bottom, false, false)
        else bottomXTK
      }
      else new XTK(tk, isExact, isNonNull)
    }
    def apply(tk: icodes.TypeKind): XTK = apply(tk, false, false)
    def unapply(xtk: XTK): Option[Tuple3[icodes.TypeKind, Boolean, Boolean]] = {
      Some(Tuple3(xtk.tk, xtk.isExact, xtk.isNonNull))
    }
  }

  /* Used by MTFAGrowable which in turn is used during the inlining analysis. */
  case class FrameState(
    locals: Array[XTK], // safer would be Vector, or a `FunctionalArray` custom wrapper.
    stack:  Array[XTK]  // top is at index 0, includes both net stack increase and incoming stack.
  ) {
      override def equals(other: Any): Boolean = other match {
        case that: FrameState => locals.sameElements(that.locals) && stack.sameElements(that.stack)
        case _ => false
      }
      override def hashCode: Int = { // similar to j.u.Arrays.deepHashCode()
        var res = 0
        var i = 0; while(i < locals.length) { res += locals(i).hashCode; i += 1 }
        i = 0;     while(i < stack.length)  { res += stack(i).hashCode;  i += 1 }
        res
      }
      @inline def isBottom = (this eq frameLattice.bottom)
  }

  /** The type flow lattice used in MTFAGrowable. Doesn't extend SemiLattice on purpose.
   */
  object frameLattice {

    type Elem = FrameState // for informational purposes

    val emptyXTKs = Array.empty[XTK]
    val top       = FrameState(emptyXTKs, emptyXTKs) // TODO use case object
    val bottom    = FrameState(emptyXTKs, emptyXTKs)

    def lub(a: XTK, b: XTK): XTK = {
      assert(a != null, "a.tk should be REFERENCE(typeLattice.bottom)")
      assert(b != null, "b.tk should be REFERENCE(typeLattice.bottom)")
      if      (a.isBottom) b
      else if (b.isBottom) a
      else {
        val u = icodes.lub(a.tk, b.tk)
        val e = (a.isExact   && b.isExact)
        val n = (a.isNonNull && b.isNonNull)
        XTK(u, e, n)
      }
    }

    def lubArr(a: Array[XTK], b: Array[XTK]): Array[XTK] = {
      val newLength = math.max(a.length, b.length)
      var c = new Array[XTK](newLength)
      val minLength = math.min(a.length, b.length)
      var i = 0
      while(i < minLength) {
        c(i) = lub(a(i), b(i))
        i += 1
      }
      while(i < a.length) {
        assert(a(i) != null, "a(i).tk should be REFERENCE(typeLattice.bottom)")
        c(i) = a(i)
        i += 1
      }
      while(i < b.length) {
        assert(b(i) != null, "b(i).tk should be REFERENCE(typeLattice.bottom)")
        c(i) = b(i)
        i += 1
      }
      c
    }

    def lub(exceptional: Boolean)(a: FrameState, b: FrameState) = {
      if      (a.isBottom) b
      else if (b.isBottom) a
      else {
        val FrameState(env1, _) = a
        val FrameState(env2, _) = b

        val locals = lubArr(env1, env2)
        val stack: Array[XTK]  =
          if (exceptional) emptyXTKs
          else {
            assert(a.stack.length == b.stack.length,
                   "mismatched arrays of locals can be lub-ed (they are an artifact of doInline.newLocal) " +
                   "but frame-states should have identical stack heights, before merge.")
            lubArr(a.stack, b.stack)
          }

        FrameState(locals, stack)
      }
    }

  }

  abstract class SinglePassTFA {

    import icodes._

    private val STRING = REFERENCE(StringClass)

    trait AbstractTK
    case class FixedTK(xtk: XTK) extends AbstractTK
    case class StackRelTK(n: Int)       extends AbstractTK
    case class LocalRelTK(v: Int)       extends AbstractTK
    case class AArrOf(atk: AbstractTK)  extends AbstractTK
    case class AElemOf(atk: AbstractTK) extends AbstractTK

    case class Delta(
      outLocals: Array[AbstractTK],
      netStack:  Array[AbstractTK], // top is at index 0, includes only net stack increase by a BasicBlock (excludes the incoming stack)
      stackTrim: Int
    )

    def computeDelta(numLocals: Int, instrs0: List[Instruction]): Delta = {
      val outLocals = new Array[AbstractTK](numLocals)
      var outStack: List[AbstractTK] = Nil
      var stackTrim: Int = 0

          def push(atk: AbstractTK) { outStack ::= atk }
          def load(tk: TypeKind)    { outStack ::= FixedTK(XTK(tk, false, false)) }
          def xload(tk: TypeKind, isExactType: Boolean, isNonNull: Boolean) { outStack ::= FixedTK(XTK(tk, isExactType, isNonNull)) }
          def pop(): AbstractTK = {
            if(outStack.isEmpty) { val oldStackTrim = stackTrim; stackTrim += 1; StackRelTK(oldStackTrim) }
            else { val h = outStack.head; outStack = outStack.tail; h }
          }
          def pop2() { pop(); pop() }
          def pop3() { pop(); pop(); pop() }
          def popN(n: Int) { var i = n; while(i > 0) { pop(); i -= 1} }
          def elemOf(atk: AbstractTK): AbstractTK = {
            atk match {
              case FixedTK(arr) =>
                val componentTK = arr.tk.asInstanceOf[icodes.ARRAY].elem;
                FixedTK(XTK(componentTK, false, false))
              case AArrOf(atk)  => atk
              case _            => AElemOf(atk)
            }
          }

          def computeCallPrim(primitive: Primitive) {
            primitive match {
              case Negation(kind)       => pop();  load(kind)
              case Test(_, kind, zero)  => pop();  if (!zero) pop(); load(BOOL)
              case Comparison(_, _)     => pop2(); load(INT)

              case Arithmetic(op, kind) =>
                pop();
                if (op != NOT) { pop() }
                val k = kind match {
                  case BYTE | SHORT | CHAR => INT
                  case _ => kind
                }
                load(k)

              case Logical(op, kind)    => pop2(); load(kind)
              case Shift(op, kind)      => pop2(); load(kind)
              case Conversion(src, dst) => pop();  load(dst)
              case ArrayLength(kind)    => pop();  load(INT)
              case StartConcat          => load(ConcatClass) // TODO consider isExact == isNonNull == true
              case EndConcat            => pop();  load(STRING)
              case StringConcat(el)     => pop2(); load(ConcatClass)
            }
          }

      var instrs = instrs0
      while(!instrs.isEmpty) {
        val i  = instrs.head

        import opcodes._

        i match {

          case THIS(clasz)                 =>
            xload(toTypeKind(clasz.tpe),
                  false, // TODO not sure about isExactType == true. Conservatively picking false.
                  true)

          case CONSTANT(const)             =>
            val isNull = (const.value == null)
            val isRef  = List(StringTag, ClazzTag, EnumTag).contains(const.tag)
            xload(toTypeKind(const.tpe),
                  true,
                  !isNull && !isRef) // TODO actually, can a string constant be null? And what about an enum literal?

          case LOAD_ARRAY_ITEM(kind)       => pop(); push(elemOf(pop()))

          case LOAD_LOCAL(local)           =>
            val t = outLocals(local.index)
            if(t == null) { push(LocalRelTK(local.index)) }
            else          { push(t) }

          case LOAD_FIELD(field, isStatic) => if (!isStatic) pop(); load(toTypeKind(field.tpe))

          case LOAD_MODULE(module)         =>
            xload(toTypeKind(module.tpe),
                  true,
                  false) // giving isNonNull == true would place us at odds with the JVM's assumption that module-fields may hold nulls.

          case STORE_ARRAY_ITEM(kind)      => pop3()
          case STORE_LOCAL(local)          => outLocals(local.index) = pop()
          case STORE_THIS(_)               => pop()
          case STORE_FIELD(_, isStatic)    => if (isStatic) pop() else pop2()
          case CALL_PRIMITIVE(primitive)   => computeCallPrim(primitive)
          case cm : CALL_METHOD            => popN(cm.consumed); cm.producedTypes foreach load
          case BOX(kind)                   => pop(); xload(BOXED(kind), true, true)
          case UNBOX(kind)                 => pop(); load(kind)
          case NEW(kind)                   => xload(kind, true, true)
          case CREATE_ARRAY(elem, dims)    => popN(dims); xload(ARRAY(elem), true, true)
          case IS_INSTANCE(tpe)            => pop(); load(BOOL)
          case CHECK_CAST(tpe)             => pop(); load(tpe) // no assurances about type-exactness or non-nullness.
          case SWITCH(tags, labels)        => pop()
          case JUMP(whereto)               => ()
          case CJUMP(_, _, _, _)           => pop2()
          case CZJUMP(_, _, _, _)          => pop()
          case RETURN(kind)                => if (kind != UNIT) { pop() }
          case THROW(_)                    => pop()
          case DROP(_)                     => pop()
          case DUP(_)                      => val t = pop(); push(t); push(t)
          case MONITOR_ENTER()             => pop()
          case MONITOR_EXIT()              => pop()
          case SCOPE_ENTER(_)              => ()
          case SCOPE_EXIT(_)               => ()
          case LOAD_EXCEPTION(clasz)       =>
            outStack = Nil;
            load(toTypeKind(clasz.tpe)) // no assurances about type-exactness or non-nullness.
          case _                           => dumpClassesAndAbort("Unknown instruction: " + i)
        }

        instrs = instrs.tail
      }

      Delta(outLocals, outStack.toArray, stackTrim)
    }

    def applyDelta(input: FrameState, delta: Delta): FrameState = {
      val mostCurrentNumLocals = delta.outLocals.size
      assert(input.locals.size <= delta.outLocals.size, "input.locals needs to be extended when doInline.newLocal added vars, but never contracted.")

          def xlate(atk: AbstractTK): XTK = {
            atk match {
              case FixedTK(xtk)    => xtk
              case StackRelTK(n)   => input.stack(n)
              case LocalRelTK(v)   => val loc = input.locals(v); assert(loc != null, "should be REFERENCE(typeLattice.bottom)"); loc
              case AArrOf(nested)  =>
                // Some rationale: in `computeDelta`, CREATE_ARRAY results in a `Fixed` type-repr, not an `AArrOf`.
                // Thus nobody ever instantiates an `AArrOf`.
                // Still, given that CREATE_ARRAY is the only instruction that might result in `AArrOf`,
                // we translate it anyway with isExactType == isNonNull == true.
                XTK(ARRAY(xlate(nested).tk), true, true)
              case AElemOf(nested) =>
                val componentTK = xlate(nested).tk.asInstanceOf[icodes.ARRAY].elem
                XTK(componentTK, false, false)
            }
          }

      val newLocals = {
        val res =
          if(input.locals.size < mostCurrentNumLocals) {
            val arr = new Array[XTK](mostCurrentNumLocals)
            val ilCnt = input.locals.length
            java.lang.System.arraycopy(input.locals, 0, arr, 0, ilCnt)
            var j = ilCnt; while(j < arr.length) { arr(j) = bottomXTK; j += 1 }

            arr
          } else {
            input.locals.clone
          }
        var i = 0
        while(i < delta.outLocals.length) {
          val d = delta.outLocals(i)
          if(d != null) { res(i) = xlate(d) }
          i += 1
        }
        res
      }
      val nonTrimmed = input.stack.length - delta.stackTrim
      val newStack   = new Array[XTK](nonTrimmed + delta.netStack.length)
      val addedStack = delta.netStack map xlate;

      java.lang.System.arraycopy( addedStack,               0, newStack,                 0, addedStack.length)
      java.lang.System.arraycopy(input.stack, delta.stackTrim, newStack, addedStack.length,        nonTrimmed)

      FrameState(newLocals, newStack)
    }

  }

  case class CallsiteInfo(bb: icodes.BasicBlock, receiver: Symbol, stackLength: Int, concreteMethod: Symbol, lastParamFirst: Array[icodes.TypeKind])

  /**

    A type-flow analysis on a method computes in- and out-flows for each basic block (e.g., that's what MethodTFA does).

    For the purposes of Inliner, doing so guarantees that an abstract typestack-slot is available by the time an inlining candidate (a CALL_METHOD instruction) is visited.
    Like MethodTFA, MTFAGrowable also aims at performing such analysis on CALL_METHOD instructions, with some differences to make it faster:

      (a) early screening is performed while the type-flow is being computed (in an override of `blockTransfer`) by testing a subset of the conditions that Inliner checks later.
          The reasoning here is: if the early check fails at some iteration, there's no chance a follow-up iteration (with a yet more lub-ed typestack-slot) will succeed.
          Failure is sufficient to remove that particular CALL_METHOD from the typeflow's `remainingCALLs`.
          A forward note: in case inlining occurs at some basic block B, all blocks reachable from B get their CALL_METHOD instructions considered again as candidates in the next round
          (on the expectation that more precise types can be computed).

      (b) in case the early check does not fail, no conclusive decision can be made, thus the CALL_METHOD stays `isOnwatchlist`.

    In other words, `remainingCALLs` tracks those callsites that later on (once the DFA has converged) Inliner will focus on.
    `remainingCALLs` also caches info about the typestack just before the callsite, so as to spare Inliner computing them again.

    Besides caching as described above, a further optimization involves skipping those basic blocks
    whose in-flow and out-flow isn't needed anyway, as described next.

    A basic block lacking a callsite in `remainingCALLs` won't lead to inlining, calling into question the effort to compute the block's in- and out-flow.
    But as we know from the way type-flows are computed, computing the in- and out-flow for a basic block relies in general on those of other basic blocks.
    How to find the right balance, so as not to skip computing type-flow information that is actually needed?
    In detail, we want to focus on that sub-graph of the CFG such that control flow may reach a remaining candidate callsite.
    The basic blocks that aren't part of that subgraph can be skipped altogether. That's why:
       - `combWorklist()` in `MTFAGrowable` now checks for inclusion of a basic block in `relevantBBs`
       - same check is performed before adding a block to the worklist, and as part of choosing successors.
    The bookkeeping supporting on-the-fly pruning of irrelevant blocks requires overridding most methods of the dataflow-analysis.

    The rest of the story takes place in Inliner, which does not visit all of the method's basic blocks but only on those represented in `remainingCALLs`.

    @author Miguel Garcia, http://lampwww.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/

   */
  final class MTFAGrowable extends SinglePassTFA {

    import icodes._

    var method: IMethod = _
    def numLocals: Int  = method.locals.size // `Inliner.CallerCalleeInfo.doInline()` adds a local for each formal param of an inlined method.

    val worklist: mutable.Set[BasicBlock]        = new mutable.LinkedHashSet
    val in:  mutable.Map[BasicBlock, FrameState] = new mutable.HashMap
    val out: mutable.Map[BasicBlock, FrameState] = new mutable.HashMap
    val visited: mutable.HashSet[BasicBlock]     = new mutable.HashSet

    val remainingCALLs = mutable.Map.empty[opcodes.CALL_METHOD, CallsiteInfo]
    val isRemainingBB  = mutable.Set.empty[BasicBlock]

    var callerLin: Traversable[BasicBlock] = null

    // by piggybacking on the TFA, some calls can be resolved from virtual-dispatch to static-dispatch.
    val resolvedInvocations = mutable.Map.empty[opcodes.CALL_METHOD, opcodes.CALL_METHOD]
    val resolvedBlocks      = mutable.Set.empty[BasicBlock]

    def run {
      timer.start; combWorklist(); val t = timer.stop

      /* Now that the forward-analysis has converged, all inlining candidates are tracked in map `remainingCALLs`,
         which maps callsites to typestack-information just before the callsite in question (see `CallsiteInfo`).
         In order to keep `analyzeMethod()` simple, we collect in `isRemainingBB` those basic blocks containing one or more candidates. */
      isRemainingBB.clear()
      for(rc <- remainingCALLs) { isRemainingBB += rc._2.bb }

      if (settings.debug.value) {
        for(b <- callerLin; if (b != method.startBlock) && isRemainingBB(b)) {
          assert(visited.contains(b),
                 "Block " + b + " in " + this.method + " has input equal to bottom -- not visited? .." + visited)
        }
      }
    }

    var shrinkedWatchlist = false

    /*
      In this method information cached elsewhere is used (as described next) to realize three shortcuts:
        (1) when applying the transfer-function, sometimes it need not be applied till the very last instruction
        (2) upong visiting a callsite as part of applying the transfer-function, some decisions can be made:
            (a) discard the callsite from the list of candidates, and/or
            (b) collect information about the simulated type-stack for later use, and/or
            (c) hint whether the callsite can be resolved from invoke-virtual to invoke-static.

      Regarding (1)
      -------------
        `combWorklist()` already takes care of skipping computing type-flows for blocks we don't need
        (ie blocks not tracked in `relevantBBs`, which is initially populated by `putOnRadar`).
        Beyond that, `blockTransfer()` can also skip some work by not updating the frame-state till the very last instruction in this basic block.
        Frequently the last CALL_METHOD of interest ("of interest" equates to "being tracked in `isOnWatchlist`) isn't the last instruction on the block.
        There are cases where the typeflows computed past this `lastInstruction` are needed, and cases where they aren't.
        The reasoning behind this decision is described in `populatePerimeter()`.
        To know at which instruction to stop, `blockTransfer()` first needs to know whether `isOnPerimeter(BasicBlock)` and  then `lastInstruction(b)`.
        Both are ready for use by now, prepared by `populatePerimeter()`. The other role `blockTransfer()` plays in connection to this
        is setting `shrinkedWatchlist = true` upon removing a callsite from the candidates list,
        which prompts `combWorklist()` to update `isOnPerimeter` and  `lastInstruction`.

      Regarding (2)
      -------------
        Upon visiting a CALL_METHOD that's an inlining candidate, some information about the pre-instruction typestack is collected for future use.
        That is, unless the candidacy test fails. The reasoning here is: if such early check fails at some iteration, there's no chance a follow-up iteration
        (with a yet more lub-ed typestack-slot) will succeed. In case of failure we can safely remove the CALL_METHOD from both `isOnWatchlist` and `remainingCALLs`.

     */
    def blockTransfer(b: BasicBlock, in: FrameState): FrameState = {
      var result = FrameState(in.locals, in.stack)

      val stopAt = if(isOnPerimeter(b)) lastInstruction(b) else null;
      var isPastLast = false

      var instrs = b.toList
      while(!isPastLast && !instrs.isEmpty) {
        val i  = instrs.head

        if(isOnWatchlist(i)) {
          val cm = i.asInstanceOf[opcodes.CALL_METHOD]
          val msym = cm.method
          // -----------------------------------------------------------------------
          // (2.b) collect information about the simulated type-stack for later use.
          // -----------------------------------------------------------------------
          val paramsLength   = msym.info.paramTypes.size
          val lastParamFirst = result.stack.take(paramsLength + 1) // includes receiver (as last element)
          assert(lastParamFirst.last == result.stack.drop(paramsLength).head,
                 "two different ways to get to the same call-receiver don't match.")
          val receiver = lastParamFirst.last match {
            case XTK(REFERENCE(s), _, _) => s
            case _                       => NoSymbol // e.g. the scrutinee is BOX(s) or ARRAY
          }
          val concreteMethod = inliner.lookupImplFor(msym, receiver)
          val canDispatchStatic = ( inliner.isClosureClass(receiver) || concreteMethod.isEffectivelyFinal || receiver.isEffectivelyFinal )
          // -------------------------------------------------------
          // (2.a) discard the callsite from the list of candidates.
          // -------------------------------------------------------
          if(canDispatchStatic && !blackballed(concreteMethod)) {
            remainingCALLs += Pair(cm, CallsiteInfo(b, receiver, result.stack.length, concreteMethod, (lastParamFirst map { xtk => xtk.tk} ) ))
          } else {
            remainingCALLs.remove(cm)
            isOnWatchlist.remove(cm)
            shrinkedWatchlist = true
          }
          // -------------------------------------------------------------------------------------
          // (2.c) hint whether the callsite can be resolved from invoke-virtual to invoke-static.
          // -------------------------------------------------------------------------------------
          if((concreteMethod != msym) && !cm.style.isSuper) {
            // TODO skip in case resolvedInvocations.isDefinedAt(cm), add assert about similar contents.
            assert(cm.style.hasInstance, "All MTFAGrowable.isPreCandidate were supposed to have an instance as receiver.")
            // TODO `newStyle` should ideally be `opcodes.Static(true)` when `canDispatchStatic` but usually can't,
            //      because the type-flow algorithm in the JVM complains the receiver might be null ("Illegal use of nonvirtual function call").
            val newStyle = /* TODO if(canDispatchStatic) icodes.opcodes.Static(true) else */ cm.style
            val newCM    = cm.copy(concreteMethod, newStyle)
            // TODO not setting setHostClass() nor setTargetTypeKind() because I don't know what they are for.
            resolvedInvocations += (cm -> newCM)
            resolvedBlocks += b
          } else {
            // a previous iteration of the DFA might have added `cm` and now its more-lubbed receiver doesn't warrant de-virtualization anymore.
            resolvedInvocations.remove(cm)
          }
        }

        isPastLast = (i eq stopAt)

        if(!isPastLast) {
          result = updatedFrame(result, i)
          instrs = instrs.tail
        }
      }

      result
    } // end of method blockTransfer

    private def updatedFrame(frame: FrameState, i: Instruction): FrameState = {
      val delta   = computeDelta(numLocals, List(i))
      val updated = applyDelta(frame, delta)
      updated
    }

    val isOnWatchlist = mutable.Set.empty[Instruction]

    /* Each time CallerCalleeInfo.isSafeToInline determines a concrete callee is unsafe to inline in the current caller,
       the fact is recorded in this TFA instance for the purpose of avoiding devoting processing to that callsite next time.
       The condition of "being unsafe to inline in the current caller" sticks across inlinings and TFA re-inits
       because it depends on the instructions of the callee, which stay unchanged during the course of `analyzeInc(caller)`
       (with the caveat of the side-effecting `makePublic` in `helperIsSafeToInline`).*/
    val knownUnsafe = mutable.Set.empty[Symbol]
    val knownSafe   = mutable.Set.empty[Symbol]
    val knownNever  = mutable.Set.empty[Symbol] // `knownNever` needs be cleared only at the very end of the inlining phase (unlike `knownUnsafe` and `knownSafe`)
    @inline final def blackballed(msym: Symbol): Boolean = { knownUnsafe(msym) || knownNever(msym) }

    val relevantBBs   = mutable.Set.empty[BasicBlock]

    /*
     * Rationale to prevent some methods from ever being inlined:
     *
     *   (1) inlining getters and setters results in exposing a private field,
     *       which may itself prevent inlining of the caller (at best) or
     *       lead to situations like SI-5442 ("IllegalAccessError when mixing optimized and unoptimized bytecode")
     *
     *   (2) only invocations having a receiver object are considered (ie no static-methods are ever inlined).
     *       This is taken care of by checking `isDynamic` (ie virtual method dispatch) and `Static(true)` (ie calls to private members)
     */
    private def isPreCandidate(cm: opcodes.CALL_METHOD): Boolean = {
      val msym  = cm.method
      val style = cm.style

      !blackballed(msym)  &&
      !msym.isConstructor &&
      (!msym.isAccessor || inliner.isClosureClass(msym.owner)) &&
      (style.isDynamic  || (style.hasInstance && style.isStatic))
    }

    /** Initialize the in/out maps for the analysis of the given method. */
    def init(m: icodes.IMethod) {
      in.clear; out.clear; worklist.clear; visited.clear;
      method = m
      worklist += m.startBlock
      worklist ++= (m.exh map (_.startBlock))
      m foreachBlock { b =>
        in(b)  = frameLattice.bottom
        out(b) = frameLattice.bottom
      }

      val localsOnEntry = {
        var idx = 0
        val res = new Array[XTK](numLocals)
        for(l <- m.locals) { l.index = idx; res(idx) = bottomXTK; idx += 1 }
        for(p <- m.params) { res(p.index) = XTK(p.kind) }
        res
      }
      // start block has var bindings for each of its parameters
      in(m.startBlock) = FrameState(localsOnEntry, frameLattice.emptyXTKs)

      m.exh foreach { e =>
        in(e.startBlock) = FrameState(localsOnEntry, frameLattice.emptyXTKs)
      }

      resolvedInvocations.clear()
      resolvedBlocks.clear()
      remainingCALLs.clear()
      knownUnsafe.clear()
      knownSafe.clear()
      // initially populate the watchlist with all callsites standing a chance of being inlined
      isOnWatchlist.clear()
      relevantBBs.clear()
        /* TODO Do we want to perform inlining in non-finally exception handlers?
         * Seems counterproductive (the larger the method the less likely it will be JITed.
         * It's not that putting on radar only `linearizer linearizeAt (m, m.startBlock)` makes for much shorter inlining times (a minor speedup nonetheless)
         * but the effect on method size could be explored.  */
      putOnRadar(m.linearizedBlocks(linearizer))
      populatePerimeter()
      assert(relevantBBs.isEmpty || relevantBBs.contains(m.startBlock), "you gave me dead code")
    }

    def conclusives(b: BasicBlock): List[opcodes.CALL_METHOD] = {
      knownBeforehand(b) filter { cm => inliner.isMonadicMethod(cm.method) || inliner.hasInlineAnn(cm.method) }
    }

    def knownBeforehand(b: BasicBlock): List[opcodes.CALL_METHOD] = {
      b.toList collect { case c : opcodes.CALL_METHOD => c } filter { cm => isPreCandidate(cm) && isReceiverKnown(cm) }
    }

    private def isReceiverKnown(cm: opcodes.CALL_METHOD): Boolean = {
      cm.method.isEffectivelyFinal && cm.method.owner.isEffectivelyFinal
    }

    private def putOnRadar(blocks: Traversable[BasicBlock]) {
      for(bb <- blocks) {
        val preCands = bb.toList collect {
          case cm : opcodes.CALL_METHOD
            if isPreCandidate(cm) /* && !isReceiverKnown(cm) */
          => cm
        }
        isOnWatchlist ++= preCands
      }
      relevantBBs ++= blocks
    }

    /* the argument is also included in the result */
    private def transitivePreds(b: BasicBlock): Set[BasicBlock] = { transitivePreds(List(b)) }

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

    /* A basic block B is "on the perimeter" of the current control-flow subgraph if none of its successors belongs to that subgraph.
     * In that case, for the purposes of inlining, we're interested in the typestack right before the last inline candidate in B, not in those afterwards.
     * In particular we can do without computing the outflow at B. */
    private def populatePerimeter() {
      isOnPerimeter.clear()
      var done = true
      do {
        val (frontier, toPrune) = (relevantBBs filter hasNoRelevantSuccs) partition isWatching
        isOnPerimeter ++= frontier
        relevantBBs   --= toPrune
        done = toPrune.isEmpty
      } while(!done)

      lastInstruction.clear()
      for (b <- isOnPerimeter; lastIns = b.toList.reverse find isOnWatchlist) {
        lastInstruction += (b -> lastIns.get.asInstanceOf[opcodes.CALL_METHOD])
      }

      // assertion: "no relevant block can have a predecessor that is on perimeter"
      assert((for (b <- relevantBBs; if transitivePreds(b.predecessors) exists isOnPerimeter) yield b).isEmpty)
    }

    private val isOnPerimeter   = mutable.Set.empty[BasicBlock]
    private val lastInstruction = mutable.Map.empty[BasicBlock, opcodes.CALL_METHOD]

    def hasNoRelevantSuccs(x: BasicBlock): Boolean = { !(x.successors exists relevantBBs) }

    def isWatching(x: BasicBlock): Boolean = (x.toList exists isOnWatchlist)




    /**

      This method is invoked after one or more inlinings have been performed in basic blocks whose in-flow is non-bottom (this makes a difference later).
      What we know about those inlinings is given by:

        - `staleOut`: These are the blocks where a callsite was inlined.
                      For each callsite, all instructions in that block before the callsite were left in the block, and the rest moved to an `afterBlock`.
                      The out-flow of these basic blocks is thus in general stale, that's why we'll add them to the TFA worklist.

        - `inlined` : These blocks were spliced into the method's CFG as part of inlining. Being new blocks, they haven't been visited yet by the typeflow analysis.

        - `staleIn` : These blocks are what `doInline()` calls `afterBlock`s, ie the new home for instructions that previously appearead
                      after a callsite in a `staleOut` block.

      Based on the above information, we have to bring up-to-date the caches that `forwardAnalysis` and `blockTransfer` use to skip blocks and instructions.
      Those caches are `relevantBBs` and `isOnPerimeter` (for blocks) and `isOnWatchlist` and `lastInstruction` (for CALL_METHODs).
      Please notice that all `inlined` and `staleIn` blocks are reachable from `staleOut` blocks.

      The update takes place in two steps:

        (1) `staleOut foreach { so => putOnRadar(linearizer linearizeAt (m, so)) }`
            This results in initial populations for `relevantBBs` and `isOnWatchlist`.
            Because of the way `isPreCandidate` reuses previous decision-outcomes that are still valid,
            this already prunes some candidates standing no chance of being inlined.

        (2) `populatePerimeter()`
            Based on the CFG-subgraph determined in (1) as reflected in `relevantBBs`,
            this method detects some blocks whose typeflows aren't needed past a certain CALL_METHOD
            (not needed because none of its successors is relevant for the purposes of inlining, see `hasNoRelevantSuccs`).
            The blocks thus chosen are said to be "on the perimeter" of the CFG-subgraph.
            For each of them, its `lastInstruction` (after which no more typeflows are needed) is found.

     */
    def reinit(m: icodes.IMethod, staleOut: List[BasicBlock], inlined: collection.Set[BasicBlock], staleIn: collection.Set[BasicBlock]) {
      if (this.method == null || this.method.symbol != m.symbol) {
        init(m)
        return
      } else if(staleOut.isEmpty && inlined.isEmpty && staleIn.isEmpty) {
        // this promotes invoking reinit if in doubt, no performance degradation will ensue!
        return;
      }

      worklist.clear // calling reinit(f: => Unit) would also clear visited, thus forgetting about blocks visited before reinit.

      // asserts conveying an idea what CFG shapes arrive here:
      //   staleIn foreach (p => assert( !in.isDefinedAt(p), p))
      //   staleIn foreach (p => assert(!out.isDefinedAt(p), p))
      //   inlined foreach (p => assert( !in.isDefinedAt(p), p))
      //   inlined foreach (p => assert(!out.isDefinedAt(p), p))
      //   inlined foreach (p => assert(!p.successors.isEmpty || p.lastInstruction.isInstanceOf[icodes.opcodes.THROW], p))
      //   staleOut foreach (p => assert(  in.isDefinedAt(p), p))

      // remainingCALLs.clear()
      isOnWatchlist.clear()
      relevantBBs.clear()

      // never rewrite in(m.startBlock)
      staleOut foreach { b =>
        enqueue(b)
        out(b) = frameLattice.bottom
      }
      // nothing else is added to the worklist, bb's reachable via succs will be tfa'ed
      blankOut(inlined)
      blankOut(staleIn)
      // no need to add startBlocks from m.exh

      staleOut foreach { so => putOnRadar(linearizer linearizeAt (m, so)) }
      populatePerimeter()

    } // end of method reinit

    /* this is not a general purpose method to add to the worklist,
     * because the assert is expected to hold only when called from MTFAGrowable.reinit() */
    private def enqueue(b: BasicBlock) {
      assert(in(b) ne frameLattice.bottom)
      if(!worklist.contains(b)) { worklist += b }
    }

    /* this is not a general purpose method to add to the worklist,
     * because the assert is expected to hold only when called from MTFAGrowable.reinit() */
    private def enqueue(bs: Traversable[BasicBlock]) {
      bs foreach enqueue
    }

    private def blankOut(blocks: collection.Set[BasicBlock]) {
      blocks foreach { b =>
        in(b)  = frameLattice.bottom
        out(b) = frameLattice.bottom
      }
    }

    /*
      This is basically the plain-old forward-analysis part of a dataflow algorithm,
      adapted to skip non-relevant blocks (as determined by `reinit()` via `populatePerimeter()`).

      The adaptations are:

        - only relevant blocks dequeued from the worklist move on to have the transfer function applied

        - `visited` now means the transfer function was applied to the block,
          but please notice that this does not imply anymore its out-flow to be different from bottom,
          because a block on the perimeter will have per-instruction typeflows computed only up to its `lastInstruction`.
          In case you need to know whether a visted block `v` has been "fully visited", evaluate `out(v) ne typeflowLattice.bottom`

        - given that the transfer function may remove callsite-candidates from the watchlist (thus, they are not candidates anymore)
          there's an opportunity to detect whether a previously relevant block has been left without candidates.
          That's what `shrinkedWatchlist` detects. Provided the block was on the perimeter, we know we can skip it from now on,
          and we can also try reducing the CFG-subgraph of interest, by finding a new perimeter (see `populatePerimeter()`).
     */
    def combWorklist() {
      while (!worklist.isEmpty && relevantBBs.nonEmpty) {
        val point = worklist.iterator.next; worklist -= point;
        if(relevantBBs(point)) {
          shrinkedWatchlist = false
          val output = blockTransfer(point, in(point))
          visited += point;
          if(isOnPerimeter(point)) {
            if(shrinkedWatchlist && !isWatching(point)) {
              relevantBBs -= point;
              populatePerimeter()
            }
          } else {
            val propagate = ((frameLattice.bottom == out(point)) || output != out(point))
            if (propagate) {
              out(point) = output
              val succs = point.successors filter relevantBBs
              succs foreach { p =>
                assert((p.predecessors filter isOnPerimeter).isEmpty)
                val updated = frameLattice.lub(p.exceptionHandlerStart)(output, in(p))
                if(updated != in(p)) {
                  in(p) = updated
                  enqueue(p)
                }
              }
            }
          }
        }
      }
      worklist.clear()
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
