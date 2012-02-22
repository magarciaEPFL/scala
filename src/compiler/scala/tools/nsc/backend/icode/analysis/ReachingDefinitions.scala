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

  sealed case class InstrPos(bb: BasicBlock, idx: Int)

  /** The lattice for reaching definitions.
   */
  object rdefLattice extends SemiLattice {
    type Definition = (Local, BasicBlock, Int)
    type Elem       = IState[collection.Map[Local, collection.Set[InstrPos]], Stack]
    type Stack      = List[collection.Set[InstrPos]]

    def emptyLocals() = mutable.Map.empty[Local, collection.Set[InstrPos]]

    val top: Elem    = IState(null, Nil)
    val bottom: Elem = IState(null, Nil)

    val exceptionHandlerStack = Nil

    /** The least upper bound is:
     *    - local-wise union of sets of store instructions (for locals), and
     *    - pairwise union of push instrctions (for stacks).
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
          val lv = emptyLocals()
          val vset = a.vars.keySet ++ b.vars.keySet
          for(v <- vset) {
            val stores1 = a.vars.getOrElse(v, Set())
            val stores2 = b.vars.getOrElse(v, Set())
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
    import lattice.{ Stack, Elem }
    private var method: IMethod = _

    // in a map entry, its value (loc -> idx) denotes the last assignment in block `b` to local `loc`. The index of that STORE_LOCAL instruction in `b` is `idx`.
    private val gen      = mutable.Map[BasicBlock, collection.Map[Local, Int]]()

    /*
     * Regarding the operand stack, the summary information computed by `genAndKill()` consists of
     * a "stack delta" (possibly empty) placed on top of (the entry stack with some slots dropped).
     * The first piece of information (stack delta) is tracked in `outStack` while the latter (number of slots to drop) is tracked in `drops`.
     */
    private val drops    = mutable.Map[BasicBlock, Int]()
    private val outStack = mutable.Map[BasicBlock, Stack]()

    // var yardstick: global.analysis.MethodTFA = null;

    def init(m: IMethod) {
      this.method = m

      gen.clear()
      drops.clear()
      outStack.clear()

      m foreachBlock { b =>
        val (g, d, st) = genAndKill(b)
        gen      += (b -> g)
        drops    += (b -> d)
        outStack += (b -> st)
      }

      init {

        worklist  += m.startBlock
        worklist ++= (m.exh map (_.startBlock))

        m foreachBlock { b =>
          in(b)  = lattice.bottom
          out(b) = lattice.bottom
        }

        // a parameter won't be a STORE_LOCAL argument, but the start block requires a non-bottom lattice elem as starting point
        in(m.startBlock)  = lattice.IState(lattice.emptyLocals(), Nil)

        m.exh foreach { e =>
          // unlike typeStackLattice.exceptionHandlerStack, we use Nil instead. A comment in blockTransfer() mentions why.
          in(e.startBlock) = lattice.IState(lattice.emptyLocals(), lattice.exceptionHandlerStack)
        }
      }

      // yardstick = new global.analysis.MethodTFA(m)
      // yardstick.run

    }

    import opcodes._

    private def genAndKill(b: BasicBlock): (collection.Map[Local, Int], Int, Stack) = {
      var depth, drops = 0
      var stackOut: Stack = Nil
      var genSet  = Map.empty[Local, Int]

      for ((instr, idx) <- b.toList.zipWithIndex) {
        instr match {
          case STORE_LOCAL(local) => genSet += (local -> idx)
          case _                  => ()
        }
        if(!instr.isInstanceOf[LOAD_EXCEPTION]) {
          /* For a LOAD_EXCEPTION pseudo-instruction, the while loop below will push (b, idx) for it (on an empty abstract stack) */
          val consum = instr.consumed
          if(consum > depth) {
            drops += (consum - depth);
            depth = 0;
            stackOut = Nil;
          } else {
            stackOut = stackOut.drop(consum);
            depth -= consum;
          }
        }
        var prod = instr.produced
        depth += prod
        while (prod > 0) {
          stackOut ::= Set(InstrPos(b, idx))
          prod -= 1
        }
      }

      (genSet, drops, stackOut)
    }

    override def run() {
      forwardAnalysis(blockTransfer)

      gen.clear()      // initialized in init() and used (only) in blockTransfer()
      drops.clear()    // ditto
      outStack.clear() // ditto

      if (settings.debug.value) {
        linearizer.linearize(method).foreach(b =>
          assert(lattice.bottom != in(b),
            "Block " + b + " in " + this.method + " has input equal to bottom -- not visited? " + in(b)
                 + ": bot: " + lattice.bottom
                 + "\nin(b) == bottom: " + (in(b) == lattice.bottom)
                 + "\nbottom == in(b): " + (lattice.bottom == in(b))));
      }
    }

    import opcodes._
    import lattice.IState

    private def blockTransfer(b: BasicBlock, in: lattice.Elem): lattice.Elem = {
      /*
       * Although typeStackLattice.exceptionHandlerStack has size 1, its ReachingDefinitionAnalysis counterpart is empty
       * due to differences in the way LOAD_EXCEPTION is handled by blockTransfer() in TypeFlowAnalysis and ReachingDefinitionAnalysis.
       *
       *  if(b.exceptionHandlerStart) assert(in.stack.size == 0, "gotcha0a")
       *  else assert(in.stack.size == yardstick.in(b).stack.length, "gotcha1")
       *
       */
      // FYI killSet == gen(b).keySet
      val mostRecentDefs = for( (loc, idx) <- gen(b) ) yield (loc -> Set(InstrPos(b,  idx)))
      val updLocals = in.vars ++ mostRecentDefs
      val updStack  = outStack(b) ::: in.stack.drop(drops(b))

      val res = IState(updLocals, updStack)
      // assert(res.stack.size == yardstick.out(b).stack.length, "gotcha2")
      res
    }

    /** Return the reaching definitions corresponding to the point after idx. */
    def interpret(b: BasicBlock, idx: Int, in: lattice.Elem): Elem = {
      var locals: collection.Map[Local, collection.Set[InstrPos]] = in.vars
      var stack  = in.stack
      val instr  = b(idx)

      instr match {
        case STORE_LOCAL(loc) =>
          locals = (locals ++ Map(loc -> Set(InstrPos(b, idx))))
          stack = stack.drop(instr.consumed)
        case LOAD_EXCEPTION(_) =>
          stack = lattice.exceptionHandlerStack // Set(InstrPos(b, idx)) will be pushed for this instruction in a moment
        case _ =>
          stack = stack.drop(instr.consumed)
      }

      var prod = instr.produced
      while (prod > 0) {
        stack ::= Set(InstrPos(b, idx))
        prod -= 1
      }

      IState(locals, stack)
    }

    /** Return the instructions that produced the 'm' elements on the stack, below given 'depth'.
     *  for instance, findefs(bb, idx, 1, 1) returns the instructions that might have produced the
     *  value found below the topmost element of the stack.
     */
    def findDefs(bb: BasicBlock, idx: Int, m: Int, depth: Int): List[(BasicBlock, Int)] = if (idx > 0) { // TODO return collection.Set[InstrPos]
      assert(bb.closed, bb)

      var instrs = bb.getArray
      var res: collection.Set[InstrPos] = Set()
      var i = idx
      var n = m
      var d = depth
      // "I look for who produced the 'n' elements below the 'd' topmost slots of the stack"
      while (n > 0 && i > 0) {
        i -= 1
        val prod = instrs(i).produced
        if (prod > d) {
          res = res + InstrPos(bb, i)
          n   = n - (prod - d)
          instrs(i) match {
            case LOAD_EXCEPTION(_)  => ()
            case _                  => d = instrs(i).consumed
          }
        } else {
          d -= prod
          d += instrs(i).consumed
        }
      }

      if (n > 0) {
        val stack = this.in(bb).stack
        assert(stack.length >= n, "entry stack is too small, expected: " + n + " found: " + stack)
        stack.drop(d).take(n) foreach { defs =>
          res = defs ++ res
        }
      }
      for(ip <- res.toList) yield ((ip.bb, ip.idx))
    } else {
      val stack = this.in(bb).stack
      assert(stack.length >= m, "entry stack is too small, expected: " + m + " found: " + stack)
      for(sip <- stack.drop(depth).take(m); ip <- sip) yield ((ip.bb, ip.idx))
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
