/* NSC -- new scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Iulian Dragos
 */


package scala.tools.nsc
package backend.opt

import scala.collection.{ mutable, immutable }

/**
 */
abstract class DeadCodeElimination extends SubComponent {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions.RuntimePackage

  val phaseName = "dce"

  /** Create a new phase */
  override def newPhase(p: Phase) = new DeadCodeEliminationPhase(p)

  /** Dead code elimination phase.
   */
  class DeadCodeEliminationPhase(prev: Phase) extends ICodePhase(prev) {

    def name = phaseName
    val dce = new DeadCode()

    override def apply(c: IClass) {
      if (settings.Xdce.value)
        dce.analyzeClass(c)
    }

    override def run() {
      try super.run()
      finally dce.rdef.clearCaches()
    }

  }

  /** closures that are instantiated at least once, after dead code elimination */
  val liveClosures: mutable.Set[Symbol] = new mutable.HashSet()

  /** Remove dead code.
   */
  class DeadCode {

    def analyzeClass(cls: IClass) {
      for(m <- cls.methods; if m.hasCode) {
        this.method = m
        dieCodeDie(m)
        global.closureElimination.peephole(m)
      }
    }

    val rdef = new reachingDefinitions.ReachingDefinitionsAnalysis;

    /** the current method. */
    var method: IMethod = _

    /** Useful instructions which have not been scanned yet. */
    var worklist: List[(BasicBlock, Int)] = Nil

    /** what instructions have been marked as useful? */
    val useful: mutable.Map[BasicBlock, mutable.BitSet] = perRunCaches.newMap()

    /** what local variables have been accessed at least once? */
    var accessedLocals: List[Local] = Nil

    /** Map instructions who have a drop on some control path, to that DROP instruction. */
    val dropOf: mutable.Map[(BasicBlock, Int), List[(BasicBlock, Int)]] = perRunCaches.newMap()

    def dieCodeDie(m: IMethod) {
      log("dead code elimination on " + m);
      dropOf.clear()
      m.code.blocks.clear()
      accessedLocals = m.params.reverse
      m.code.blocks ++= linearizer.linearize(m)

      rdef.init(m);
      rdef.run;

      collectRDef(m)
      mark
      sweep(m)

      accessedLocals = accessedLocals.distinct
      if (m.locals exists { loc => !accessedLocals.contains(loc) } ) {
        log("Removed dead locals: " + (m.locals diff accessedLocals))
        m.locals = accessedLocals.reverse
      }
    }

    /** collect reaching definitions and initial useful instructions for this method. */
    def collectRDef(m: IMethod): Unit = {
      worklist = Nil;
      useful.clear();

      m foreachBlock { bb =>
        useful(bb) = new mutable.BitSet(bb.size)
        var idx = 0
        val instrs = bb.getArray
        while (idx < instrs.size) {
          instrs(idx) match {
            case RETURN(_) | JUMP(_) | CJUMP(_, _, _, _) | CZJUMP(_, _, _, _) | STORE_FIELD(_, _) |
                 THROW(_)   | LOAD_ARRAY_ITEM(_) | STORE_ARRAY_ITEM(_) | SCOPE_ENTER(_) | SCOPE_EXIT(_) | STORE_THIS(_) |
                 LOAD_EXCEPTION(_) | SWITCH(_, _) | MONITOR_ENTER() | MONITOR_EXIT()
              => worklist ::= Pair(bb, idx)
            case CALL_METHOD(m1, _) if isSideEffecting(m1)
              => worklist ::= Pair(bb, idx); log("marking " + m1)
            case CALL_METHOD(m1, SuperCall(_))
              => worklist ::= Pair(bb, idx) // super calls to constructor
            case DROP(_) =>
              val foundDefs = rdef.findDefs(bb, idx, 1)
              val necessary = foundDefs exists { p =>
                val (bb1, idx1) = p
                bb1(idx1) match {
                  case CALL_METHOD(m1, _) if isSideEffecting(m1) => true
                  case LOAD_EXCEPTION(_) | DUP(_) | LOAD_MODULE(_) => true // TODO why not LOAD_ARRAY_ITEM(_) too?
                  case _ =>
                    dropOf((bb1, idx1)) = (bb,idx) :: dropOf.getOrElse((bb1, idx1), Nil)
                    // println("DROP is innessential: " + i + " because of: " + bb1(idx1) + " at " + bb1 + ":" + idx1)
                    false
                }
              }
              if (necessary) { worklist ::= Pair(bb, idx) }
            case _ => ()
          }
          idx += 1
        }
      }
    }

    /** Mark useful instructions. Instructions in the worklist are each inspected and their
     *  dependencies are marked useful too, and added to the worklist.
     */
    def mark() {
      // log("Starting with worklist: " + worklist)
      while (!worklist.isEmpty) {
        val (bb, idx) = worklist.head
        worklist = worklist.tail
        debuglog("Marking instr: \tBB_" + bb + ": " + idx + " " + bb(idx))

        val instr = bb(idx)
        if (!useful(bb)(idx)) {
          useful(bb) += idx
          dropOf.get(bb, idx) foreach {
              for ((bb1, idx1) <- _)
                useful(bb1) += idx1
          }
          instr match {
            case LOAD_LOCAL(l1) =>
              for ((bb1, idx1) <- rdef.reachers(l1, bb, idx); if !useful(bb1)(idx1)) {
                log("\tAdding " + bb1(idx1))
                worklist ::= Pair(bb1, idx1)
              }

            case nw @ NEW(REFERENCE(sym)) =>
              assert(nw.init ne null, "null new.init at: " + bb + ": " + idx + "(" + instr + ")")
              worklist ::= findInstruction(bb, nw.init)
              if (inliner.isClosureClass(sym)) {
                liveClosures += sym
              }

            // it may be better to move static initializers from closures to
            // the enclosing class, to allow the optimizer to remove more closures.
            // right now, the only static fields in closures are created when caching
            // 'symbol literals.
            case LOAD_FIELD(sym, true) if inliner.isClosureClass(sym.owner) =>
              log("added closure class for field " + sym)
              liveClosures += sym.owner

            case LOAD_EXCEPTION(_) =>
              ()

            case _ =>
              val foundDefs = rdef.findDefs(bb, idx, instr.consumed)
              for ((bb1, idx1) <- foundDefs if !useful(bb1)(idx1)) {
                log("\tAdding " + bb1(idx1))
                worklist ::= Pair(bb1, idx1)
              }
          }
        }
      }
    }

    def sweep(m: IMethod) {
      val compensations = computeCompensations(m)

      m foreachBlock { bb =>
        // Console.println("** Sweeping block " + bb + " **")
        val oldInstr = bb.toList
        bb.open
        bb.clear
        for (Pair(i, idx) <- oldInstr.zipWithIndex) {
          if (useful(bb)(idx)) {
            // log(" " + i + " is useful")
            bb.emit(i, i.pos)
            compensations.get(bb, idx) match {
              case Some(is) => is foreach bb.emit
              case None => ()
            }
            // check for accessed locals
            i match {
              case LOAD_LOCAL(l)  if !l.arg => accessedLocals ::= l
              case STORE_LOCAL(l) if !l.arg => accessedLocals ::= l
              case _ => ()
            }
          } else {
            i match {
              case NEW(REFERENCE(sym)) => log("skipped object creation: " + sym + "inside " + m)
              case _                   => ()
            }
            debuglog("Skipped: bb_" + bb + ": " + idx + "( " + i + ")")
          }
        }

        if (bb.nonEmpty) bb.close
        else log("empty block encountered")
      }
    }

    private def computeCompensations(m: IMethod): collection.Map[(BasicBlock, Int), List[DROP]] = {
      val compensations: mutable.Map[(BasicBlock, Int), List[DROP]] = new mutable.HashMap

      m foreachBlock { bb =>
        assert(bb.closed, "Open block in computeCompensations")
        foreachWithIndex(bb.toList) { (i, idx) =>
          if (!useful(bb)(idx)) {
            foreachWithIndex(i.consumedTypes.reverse) { (consumedType, depth) =>
              log("Finding definitions of: " + i + "\n\t" + consumedType + " at depth: " + depth)
              val defs = rdef.findDefs(bb, idx, 1, depth)
              for (d <- defs) {
                val (bb, idx) = d
                bb(idx) match {
                  case DUP(_) if idx > 0 =>
                    bb(idx - 1) match {
                      case nw @ NEW(_) =>
                        val init = findInstruction(bb, nw.init)
                        log("Moving DROP to after <init> call: " + nw.init)
                        compensations(init) = List(DROP(consumedType))
                      case _ =>
                        compensations(d) = List(DROP(consumedType))
                    }
                  case _ =>
                    compensations(d) = List(DROP(consumedType))
                }
              }
            }
          }
        }
      }
      compensations
    }

    private def withClosed[a](bb: BasicBlock)(f: => a): a = {
      if (bb.nonEmpty) bb.close
      val res = f
      if (bb.nonEmpty) bb.open
      res
    }

    private def findInstruction(bb: BasicBlock, i: CALL_METHOD): (BasicBlock, Int) = {
      for (b <- linearizer.linearizeAt(method, bb)) {
        val idx = b.toList indexWhere (_ eq i)
        if (idx != -1)
          return (b, idx)
      }
      abort("could not find init in: " + method)
    }

    private def isPure(sym: Symbol) = (
         (sym.isGetter && sym.isEffectivelyFinal && !sym.isLazy)
      || (sym.isPrimaryConstructor && (sym.enclosingPackage == RuntimePackage || inliner.isClosureClass(sym.owner)))
    )
    /** Is 'sym' a side-effecting method? TODO: proper analysis.  */
    private def isSideEffecting(sym: Symbol) = !isPure(sym)

  } /* DeadCode */
}
