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
      finally {
        dce.rdef.clearCaches()
        dce.worklist = Nil
        dce.useful.clear()
        dce.unaccessedLocals.clear()
        dce.droppers.clear()
      }
    }

  }

  /** closures that are instantiated at least once, after dead code elimination */
  val liveClosures: mutable.Set[Symbol] = new mutable.HashSet()

  /** Remove dead code.
   */
  class DeadCode {

    /*
     * "Blix" is mnemonic for "Block-IndeX pair"
     *
     * Two purposes for the "Blix" case class:
     *   (a) results in more readable code, and
     *   (b) should perform better than Tuple2 (because Blix is "specialized" for BasicBlock and Int components)
     */
    import reachingDefinitions.Blix

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

    /** Useful instructions whose dependencies have not been scanned yet. */
    var worklist: List[Blix] = Nil

    /** Instructions scheduled to be emitted. */
    val useful = mutable.Map.empty[BasicBlock, mutable.BitSet]

    /** local variables that can be elided due to lack of access. */
    val unaccessedLocals = mutable.Set.empty[Local]

    /** A (key, values) entry indicates for an instruction that pushes (the key, a "drop feeder"),
     *  any DROP instruction(s) (the values, "droppers") that the original instruction stream contains for that key. */
    val droppers = mutable.Map.empty[Blix, List[Blix]]

    val logEnabled = opt.logPhase

    def dieCodeDie(m: IMethod) {

      log("dead code elimination on " + m);
      droppers.clear()

      unaccessedLocals.clear()
      unaccessedLocals ++= (m.locals diff m.params) // we'll remove elems from this set upon visiting useful LOAD_LOCAL or STORE_LOCAL instructions.

      m.code.blocks.clear()
      m.code.blocks ++= linearizer.linearize(m)

      rdef.init(m);
      rdef.run;

      collectRDef(m)
      mark
      sweep(m)

      if (unaccessedLocals.nonEmpty) {
        log("Removed dead locals: " + unaccessedLocals.toList.sortBy(_.sym.id) )
        m.locals = m.locals filterNot unaccessedLocals
      }

    }

    /** collect reaching definitions and initial useful instructions for this method. */
    def collectRDef(m: IMethod): Unit = {
      /* The protocol to add to worklist is:
       *   (1) in method `collectRDef` each instruction is visited exactly once thus we add directly,
       *       noting down in `useful` that the instruction is scheduled as non-dead-code.
       *   (2) after that, in order to avoid looping endlessly upon enqueing cyclic dependencies,
       *       check `isUseful` before consing to the worklist.
       */
      worklist = Nil;
      useful.clear();

      m foreachBlock { bb =>

        useful(bb) = new mutable.BitSet(bb.size)

        var idx = 0
        val instrs = bb.getArray

        while (idx < instrs.size) {
          instrs(idx) match {
            case RETURN(_) | JUMP(_) | THROW(_) | SWITCH(_, _) |
                 CJUMP(_, _, _, _) | CZJUMP(_, _, _, _) |
                 STORE_FIELD(_, _) | // field load left out on purpose (so as do the closure elimination thing)
                 LOAD_ARRAY_ITEM(_) | STORE_ARRAY_ITEM(_) |
                 SCOPE_ENTER(_) | SCOPE_EXIT(_) |
                 STORE_THIS(_) |
                 LOAD_EXCEPTION(_) |
                 MONITOR_ENTER() | MONITOR_EXIT()
              =>
                 worklist  ::= Blix(bb, idx)
                 useful(bb) += idx
            case CALL_METHOD(m1, _) if isSideEffecting(m1)
              =>
                 worklist  ::= Blix(bb, idx); log("marking " + m1)
                 useful(bb) += idx
            case CALL_METHOD(m1, SuperCall(_))
              =>
                 worklist  ::= Blix(bb, idx) // super calls to constructor
                 useful(bb) += idx
            case DROP(_) =>
              val bx = Blix(bb, idx)
              for(rx <- rdef.findBlixes(bx, 1)) {
                // for now just track the drop instruction(s) for the value that a drop-feeding instruction pushes
                // don't add to the worklist just yet, neither the dropper nor the dropper-feeder
                // Below, `bx` is a dropper, and `rx` is a dropper-feeder.
                droppers(rx) = bx :: droppers.getOrElse(rx, Nil)
              }
            case _ => ()
          }
          idx += 1
        }
      }

    }

    @inline private def isUseful(ix: Blix): Boolean = { useful(ix.bb)(ix.idx) }

    /** Mark useful instructions. Instructions in the worklist are each inspected and their
     *  dependencies are marked useful too, and added to the worklist.
     */
    def mark() {


          def usefulize(u: Blix) {
            // making useful an instruction `u` also implies making useful all of its "droppers".
            // (which in turn will force emitting those instructions (on other control paths) on which each "dropper" depends, ie the "feeders" of the DROP)
            // that may result in redundant work at runtime (say, on some of those paths, just emitting the zero of the type being dropped would preserve correctness).
            // That optimization isn't being done yet (and would be far easier with SSA).
            for(drs <- droppers.get(u); dr <- drs) {
              assert(droppers.get(dr).isEmpty)
              consToWorklist(dr)
            }
          }

          def consToWorklist(w: Blix) {
            // rather than testing whether the instruction is on the worklist (sequential scan)
            // we retrofit the meaning of map `useful` to indicate:
            //   (a) already tagged as useful (ie it was on the worklist previously), or
            //   (b) will be tagged as useful (ie. is still on the worklist).
            if(!isUseful(w)) {
              worklist     ::= w
              useful(w.bb)  += w.idx
            }
          }


      while (!worklist.isEmpty) {

        val bx = worklist.head
        worklist = worklist.tail

        val bb  = bx.bb
        val idx = bx.idx
        debuglog("Marking instr: \tBB_" + bb + ": " + idx + " " + bb(idx))
        usefulize(bx)

        val instr = bb(idx)
        instr match {
          case LOAD_LOCAL(v) =>
            // mark as useful the instructions storing into the local being loaded.
            for (rx <- rdef.reachers(v, bx)) { consToWorklist(rx) }
            if(!v.arg) { unaccessedLocals -= v } // skip set removal for arg-locals (which aren't there to start with).

          case nw @ NEW(REFERENCE(sym)) =>
            assert(nw.init ne null, "null new.init at: " + bb + ": " + idx + "(" + instr + ")")
            consToWorklist(findInstruction(bb, nw.init))
            if (inliner.isClosureClass(sym)) {
              liveClosures += sym
            }

          // it may be better to move static initializers from closures to
          // the enclosing class, to allow the optimizer to remove more closures.
          // right now, the only static fields in closures are created when caching 'symbol literals.
          case LOAD_FIELD(sym, true) if inliner.isClosureClass(sym.owner) =>
            liveClosures += sym.owner; log("added closure class for field " + sym)

          case LOAD_EXCEPTION(_) =>
            ()

          case _ =>
            // mark as useful the instructions placing on the stack what this useful instruction consumes.
            // In particular, a DROP that has been determined to be useful will have all its "drop-feeders" marked useful too
            // as sketched in the comment for `case DROP(_)` in `collectRDef(IMethod)`.
            val foundDefs = rdef.findBlixes(bx, instr.consumed)
            for (rx <- foundDefs) { consToWorklist(rx) }
        }

        instr match {
          case STORE_LOCAL(v) if(!v.arg) => unaccessedLocals -= v // skip set removal for arg-locals (which aren't there to start with).
          case _                         => ()
        }

      }
    }

    def sweep(m: IMethod) {
      val compensations = computeCompensations(m)
      var cntElimInstrs: Int = 0

      m foreachBlock { bb =>
        val oldInstr = bb.toList
        bb.open
        bb.clear
        for (Pair(i, idx) <- oldInstr.zipWithIndex) {
          if (useful(bb)(idx)) {
            bb.emit(i, i.pos)
            compensations.get(bb, idx) match {
              case Some(is) => is foreach bb.emit
              case None     => ()
            }
          } else {
            cntElimInstrs += 1
            if(logEnabled) {
              i match {
                case NEW(REFERENCE(sym)) => log("skipped object creation: " + sym + "inside " + m)
                case _                   => ()
              }
              debuglog("Skipped: bb_" + bb + ": " + idx + "( " + i + ")")
            }
          }
        }

        if (bb.nonEmpty) bb.close
        else log("empty block encountered")
      }

      log("eliminated in method " + m + " , " + cntElimInstrs + " instructions.")
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
                        val Blix(fb, fi) = findInstruction(bb, nw.init)
                        log("Moving DROP right after <init> call: " + nw.init)
                        compensations(Pair(fb, fi)) = List(DROP(consumedType))
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

    private def findInstruction(bb: BasicBlock, i: CALL_METHOD): Blix = {
      for (b <- linearizer.linearizeAt(method, bb)) {
        val idx = b.toList indexWhere (_ eq i)
        if (idx != -1)
          return Blix(b, idx)
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
