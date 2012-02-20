/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend.icode
package analysis

import scala.collection.{ mutable, immutable }
import immutable.ListSet

/** Compute reaching definitions. We are only interested in reaching
 *  definitions for local variables, since values on the stack
 *  behave as-if in SSA form: the closest instruction which produces a value
 *  on the stack is a reaching definition.
 */
abstract class ReachingDefinitions {
  val global: Global
  import global._
  import icodes._

  /** The lattice for reaching definitions. Elements are
   *  a triple (local variable, basic block, index of instruction of that basic block)
   */
  object rdefLattice extends SemiLattice {
    type Definition = (Local, BasicBlock, Int)
    type Elem       = IState[ListSet[Definition], Stack]
    type StackPos   = ListSet[(BasicBlock, Int)]
    type Stack      = List[StackPos]

    private def referenceEqualSet(name: String) = new ListSet[Definition] with ReferenceEquality {
      override def toString = "<" + name + ">"
    }

    val top: Elem    = IState(referenceEqualSet("top"), Nil)
    val bottom: Elem = IState(referenceEqualSet("bottom"), Nil)

    val exceptionHandlerStack = Nil

    /** The least upper bound is set inclusion for locals, and pairwise set inclusion for stacks. */
    def lub2(exceptional: Boolean)(a: Elem, b: Elem): Elem = {
      if (bottom eq a) {
        if(bottom eq b) bottom
        else if(exceptional) IState(b.vars, exceptionHandlerStack)
        else b
      } else if (bottom eq b) {
        if(exceptional) IState(a.vars, exceptionHandlerStack)
        else a
      } else {
        assert(exceptional || (a.stack.size == b.stack.size), "Mismatched stacks in ReachingDefinitions.")
        val lubbedVars  = a.vars ++ b.vars
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
    import lattice.{ Definition, Stack, Elem, StackPos }
    var method: IMethod = _

    private val gen      = mutable.Map[BasicBlock, ListSet[Definition]]()
    private val kill     = mutable.Map[BasicBlock, ListSet[Local]]()
    private val drops    = mutable.Map[BasicBlock, Int]()
    private val outStack = mutable.Map[BasicBlock, Stack]()

    // for debug: var yardstick: global.analysis.MethodTFA = null;

    def init(m: IMethod) {
      this.method = m

      gen.clear()
      kill.clear()
      drops.clear()
      outStack.clear()

      m foreachBlock { b =>
        val (g, k)  = genAndKill(b)
        val (d, st) = dropsAndGen(b)

        gen      += (b -> g)
        kill     += (b -> k)
        drops    += (b -> d)
        outStack += (b -> st)
      }

      init {

        worklist += m.startBlock
        worklist ++= (m.exh map (_.startBlock))

        m foreachBlock { b =>
          in(b)  = lattice.bottom
          out(b) = lattice.bottom
        }

        m.exh foreach { e =>
          in(e.startBlock) = lattice.IState(new ListSet[Definition], lattice.exceptionHandlerStack) // unlike typeStackLattice.exceptionHandlerStack, we use Nil
        }
      }

      // for debug: yardstick = new global.analysis.MethodTFA(m)
      // for debug: yardstick.run

    }

    import opcodes._

    def genAndKill(b: BasicBlock): (ListSet[Definition], ListSet[Local]) = {
      var genSet  = ListSet[Definition]()
      var killSet = ListSet[Local]()
      for ((i, idx) <- b.toList.zipWithIndex) i match {
        case STORE_LOCAL(local) =>
          killSet = killSet + local
          genSet  = updateReachingDefinition(b, idx, genSet)
        case _ => ()
      }
      (genSet, killSet)
    }

    private def dropsAndGen(b: BasicBlock): (Int, Stack) = {
      var depth, drops = 0
      var stackOut: Stack = Nil

      for ((instr, idx) <- b.toList.zipWithIndex) {
        instr match {
          case LOAD_EXCEPTION(_)            => () // the while loop below will push (b, idx) for this pseudo-instruction (on an empty abstract stack)
          case _ =>
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
          stackOut ::= ListSet((b, idx))
          prod -= 1
        }
      }
      // Console.println("drops(" + b + ") = " + drops)
      // Console.println("stackout(" + b + ") = " + stackOut)
      (drops, stackOut)
    }

    override def run() {
      forwardAnalysis(blockTransfer)
      if (settings.debug.value) {
        linearizer.linearize(method).foreach(b => if (b != method.startBlock)
          assert(lattice.bottom != in(b),
            "Block " + b + " in " + this.method + " has input equal to bottom -- not visited? " + in(b)
                 + ": bot: " + lattice.bottom
                 + "\nin(b) == bottom: " + (in(b) == lattice.bottom)
                 + "\nbottom == in(b): " + (lattice.bottom == in(b))));
      }
    }

    import opcodes._
    import lattice.IState
    def updateReachingDefinition(b: BasicBlock, idx: Int, rd: ListSet[Definition]): ListSet[Definition] = {
      val STORE_LOCAL(local) = b(idx)

      (rd filter { case (l, _, _) => l != local }) + ((local, b, idx))
    }

    private def blockTransfer(b: BasicBlock, in: lattice.Elem): lattice.Elem = {

      /* typeStackLattice.exceptionHandlerStack has size 1, while for ReachingDefinitionAnalysis that should be zero
       * (due to differences in the way LOAD_EXCEPTION is handled by blockTransfer() in TypeFlowAnalysis and ReachingDefinitionAnalysis).  */
      // for debug: if(b.exceptionHandlerStart) assert(in.stack.size == 0, "gotcha0a")
      // for debug: else assert(in.stack.size == yardstick.in(b).stack.length, "gotcha1")

      var locals: ListSet[Definition] = (in.vars filter { case (l, _, _) => !kill(b)(l) }) ++ gen(b)
      if (locals eq lattice.bottom.vars) locals = new ListSet[Definition]
      val res = IState(locals, outStack(b) ::: in.stack.drop(drops(b)))

      // for debug: assert(res.stack.size == yardstick.out(b).stack.length, "gotcha2")

      res
    }

    /** Return the reaching definitions corresponding to the point after idx. */
    def interpret(b: BasicBlock, idx: Int, in: lattice.Elem): Elem = {
      var locals = in.vars
      var stack  = in.stack
      val instr  = b(idx)

      instr match {
        case STORE_LOCAL(l1) =>
          locals = updateReachingDefinition(b, idx, locals)
          stack = stack.drop(instr.consumed)
        case LOAD_EXCEPTION(_) =>
          stack = lattice.exceptionHandlerStack // ListSet((b, idx)) will be pushed below
        case _ =>
          stack = stack.drop(instr.consumed)
      }

      var prod = instr.produced
      while (prod > 0) {
        stack ::= ListSet((b, idx))
        prod -= 1
      }

      IState(locals, stack)
    }

    /** Return the instructions that produced the 'm' elements on the stack, below given 'depth'.
     *  for instance, findefs(bb, idx, 1, 1) returns the instructions that might have produced the
     *  value found below the topmost element of the stack.
     */
    def findDefs(bb: BasicBlock, idx: Int, m: Int, depth: Int): List[(BasicBlock, Int)] = if (idx > 0) {
      assert(bb.closed, bb)

      var instrs = bb.getArray
      var res: List[(BasicBlock, Int)] = Nil
      var i = idx
      var n = m
      var d = depth
      // "I look for who produced the 'n' elements below the 'd' topmost slots of the stack"
      while (n > 0 && i > 0) {
        i -= 1
        val prod = instrs(i).produced
        if (prod > d) {
          res = (bb, i) :: res
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
          res = defs.toList ::: res
        }
      }
      res
    } else {
      val stack = this.in(bb).stack
      assert(stack.length >= m, "entry stack is too small, expected: " + m + " found: " + stack)
      stack.drop(depth).take(m) flatMap (_.toList)
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
