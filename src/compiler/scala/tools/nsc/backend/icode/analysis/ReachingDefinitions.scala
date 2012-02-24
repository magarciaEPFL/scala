/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend.icode
package analysis

import scala.collection.{ mutable, immutable }

/** Compute reaching definitions. We are only interested in reaching
 *  definitions for local variables, since values on the stack
 *  behave as-if in SSA form: the closest instruction which produces a value
 *  on the stack is a reaching definition.
 */
abstract class ReachingDefinitions {
  val global: Global
  import global._
  import icodes._

  object rdefLattice extends SemiLattice {
    type InstrPos = Long
    type LVarsT   = Map[Local, Set[InstrPos]]
    type StackT   = List[Set[InstrPos]]
    type Elem     = IState[LVarsT, StackT]

    def emptyLocals() = Map.empty[Local, Set[InstrPos]]

    val top: Elem    = IState(null, Nil)
    val bottom: Elem = IState(null, Nil)

    val exceptionHandlerStack = Nil

    /** The least upper bound is:
     *    - per-variable union of sets of store instructions (for locals), and
     *    - pairwise union of sets of push instructions (for stacks).
     */
    def lub2(exceptional: Boolean)(a: Elem, b: Elem): Elem = {
      if (bottom eq a) {
        if(bottom eq b) bottom
        else if(exceptional) IState(b.vars, exceptionHandlerStack)
        else b
      } else if (bottom eq b) {
        if(exceptional) IState(a.vars, exceptionHandlerStack)
        else a
      } else {
        assert(exceptional || (a.stack.size == b.stack.size), "Mismatched stacks.")
        val lubbedVars  = {
          var lv = emptyLocals()
          val vset = a.vars.keySet ++ b.vars.keySet
          for(v <- vset) {
            val stores1 = a.vars.getOrElse(v, immutable.TreeSet.empty[InstrPos])
            val stores2 = b.vars.getOrElse(v, immutable.TreeSet.empty[InstrPos])
            lv += (v -> (stores1 ++ stores2))
          }
          lv
        }
        val lubbedStack =
          if (exceptional) exceptionHandlerStack
          else (a.stack, b.stack).zipped map (_ ++ _)

        IState(lubbedVars, lubbedStack)
      }
    }
  }

  class ReachingDefinitionsAnalysis extends DataFlowAnalysis[rdefLattice.type] {
    type P = BasicBlock
    val lattice = rdefLattice

    import lattice.{ Elem, InstrPos }

    private var method: IMethod = _

    private val labelled = mutable.Map.empty[Int, BasicBlock]
    private val stateAt  = mutable.Map.empty[InstrPos, Elem]

    def clearCaches() {
      labelled.clear()
      stateAt.clear()
    }

    import opcodes._

    def init(m: IMethod) {
      this.method = m
      clearCaches()

      init {

        worklist  += m.startBlock
        worklist ++= (m.exh map (_.startBlock))

        m foreachBlock { b =>
          in(b)  = lattice.bottom
          out(b) = lattice.bottom
          assert(!labelled.contains(b.label), "Two basic blocks with same label")
          labelled(b.label) = b
        }

        // a parameter won't be a STORE_LOCAL argument, but the start block requires a non-bottom lattice elem as starting point
        in(m.startBlock)  = lattice.IState(lattice.emptyLocals(), Nil)

        m.exh foreach { e =>
          // unlike typeStackLattice.exceptionHandlerStack, we use Nil instead. A comment in interpret() mentions why.
          in(e.startBlock) = lattice.IState(lattice.emptyLocals(), lattice.exceptionHandlerStack)
        }
      }

    }

    @inline val loMask = 0x00000000FFFFFFFFL
    @inline val hiMask = 0xFFFFFFFF00000000L

    @inline final def encode(bb: BasicBlock, idx: Int): Long = encode(bb.label, idx)

    @inline final def encode(a: Int, b: Int): Long = {
      val p1: Long = (0L | a) << 32
      val p2: Long = (b & loMask)
      (p1 | p2)
    }

    @inline final def decode(i: InstrPos): (Int, Int) = {
      val hi = (i >>> 32).toInt
      val lo = (i & loMask).toInt
      (hi, lo)
    }

    def toBBIdx(i: Long): (BasicBlock, Int) = {
      val (hi, lo) = decode(i)
      (labelled(hi), lo)
    }

    def toInstr(i: Long): Instruction = {
      val (hi, lo) = decode(i)
      labelled(hi).getArray(lo)
    }

    /* Positions of STORE_LOCAL instructions assigning to `v` that reach the usage of `v` at (bb, idx) */
    def reachers(v: Local, bb: BasicBlock, idx: Int): List[(BasicBlock, Int)] = {
      val defs: Set[InstrPos] = stateAt(encode(bb, idx)).vars.getOrElse(v, Set())
      defs.toList map toBBIdx
    }

    override def run() {
      forwardAnalysis(blockTransfer)

      if (settings.debug.value) {
        linearizer.linearize(method).foreach(b =>
          assert(lattice.bottom != in(b),
            "Block " + b + " in " + this.method + " has input equal to bottom -- not visited? " + in(b)
                 + ": bot: " + lattice.bottom
                 + "\nin(b) == bottom: " + (in(b) == lattice.bottom)
                 + "\nbottom == in(b): " + (lattice.bottom == in(b))));
      }
    }

    def blockTransfer(b: BasicBlock, in: lattice.Elem): lattice.Elem = {
      var result = in
      val instrs = b.getArray
      var idx = 0
      while(idx < instrs.size) {
        val instr = instrs(idx)
        val encoded = encode(b, idx)
        stateAt(encoded) = result
        result = interpret(b, encoded, instr, result)
        idx += 1
      }
      result
    }

    import lattice.IState

    /** Return the reaching definitions corresponding to the point after idx. */
    def interpret(b: BasicBlock, encoded: Long, instr: Instruction, in: lattice.Elem): Elem = {
      var updLocals: lattice.LVarsT = in.vars
      var updStack:  lattice.StackT = in.stack

      instr match {
        case STORE_LOCAL(loc) =>
          updLocals = updLocals + (loc -> Set(encoded))
          updStack  = updStack.drop(instr.consumed)
        case LOAD_EXCEPTION(_) =>
          /*
           * Although typeStackLattice.exceptionHandlerStack has size 1, its ReachingDefinitionAnalysis counterpart is empty
           * due to the way LOAD_EXCEPTION is handled (here).
           *
           * The position of this instruction will be pushed in a moment,
           * this case handler serves the purpose of avoiding calling `consumed` on LOAD_EXCEPTION which raises sys.error
           *
           */
          updStack = lattice.exceptionHandlerStack
        case _ =>
          updStack = updStack.drop(instr.consumed)
      }

      var prod = instr.produced
      while (prod > 0) {
        updStack ::= Set(encoded)
        prod -= 1
      }

      IState(updLocals, updStack)
    }

    /** Return the instructions that produced the 'm' elements on the stack, below given 'depth'.
     *  for instance, findefs(bb, idx, 1, 1) returns the instructions that might have produced the
     *  value found below the topmost element of the stack.
     */
    def findDefs(bb: BasicBlock, idx: Int, m: Int, depth: Int): List[(BasicBlock, Int)] = {
      assert(bb.closed, bb)
      var res = immutable.TreeSet.empty[Long]
      val stack = stateAt(encode(bb, idx)).stack
      assert(stack.size >= (depth + m), "entry stack is too small, expected: " + (depth + m) + " found: " + stack)
      stack.drop(depth).take(m) foreach { defs => res ++= defs }

      res.toList map toBBIdx
    }

    /** Return the definitions that produced the topmost 'm' elements on the stack,
     *  and that reach the instruction at index 'idx' in basic block 'bb'.
     */
    def findDefs(bb: BasicBlock, idx: Int, m: Int): List[(BasicBlock, Int)] =
      findDefs(bb, idx, m, 0)

    override def toString: String = {
      method.code.blocks map { b =>
        "  entry(%s) = %s\n".format(b, in(b)) +
        "   exit(%s) = %s\n".format(b, out(b))
      } mkString ("ReachingDefinitions {\n", "\n", "\n}")
    }

  }


}
