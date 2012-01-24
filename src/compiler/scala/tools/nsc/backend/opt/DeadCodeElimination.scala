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

    private val MAX_THREADS = _root_.java.lang.Runtime.getRuntime().availableProcessors()
    private var q      = new _root_.java.util.concurrent.LinkedBlockingQueue[IMethod]
    private val poison = new IMethod(NoSymbol)
    private val jobord = new Ordering[IMethod] {
      override def compare(a: IMethod, b: IMethod): Int = { a.code.blockCount.compare(b.code.blockCount) }
    }
    private var jobs = new collection.mutable.TreeSet[IMethod]()(jobord)

    override def apply(c: IClass) {
      if (settings.Xdce.value) {
        for (m <- c.methods; if m.hasCode) {
          jobs add m
        }
      }
    }

    override def run() {
      super.run() // thus unitTimings will be artificially low
      val exec = _root_.java.util.concurrent.Executors.newFixedThreadPool(MAX_THREADS)
      val workers = for(i <- 1 to MAX_THREADS) yield { val t = new DCETask(q, poison); exec.execute(t); t }
      for(m <- jobs) { q put m }
      workers foreach { w => q put poison }
      exec.shutdown()
      while(!exec.isTerminated) { exec.awaitTermination(1, _root_.java.util.concurrent.TimeUnit.MILLISECONDS) }
      workers foreach { w => liveClosures ++= w.dce.dcLiveClosures }
    }

  }

  class DCETask(q: _root_.java.util.concurrent.BlockingQueue[IMethod], poison: IMethod) extends _root_.java.lang.Runnable() {
    val dce = new DeadCode()
    def run() {
      var m: IMethod = null
      while(m ne poison) {
        m = q.take()
        if (m ne poison) { dce.analyzeMethod(m) }
      }
    }
  }

  /** closures that are instantiated at least once, after dead code elimination */
  val liveClosures: mutable.Set[Symbol] = new mutable.HashSet[Symbol]

  /** Remove dead code.
   */
  class DeadCode {

    val lnrzr: Linearizer = settings.Xlinearizer.value match {
      case "rpo"    => new ReversePostOrderLinearizer()
      case "dfs"    => new DepthFirstLinerizer()
      case "normal" => new NormalLinearizer()
      case "dump"   => new DumpLinearizer()
      case x        => global.abort("Unknown linearizer: " + x)
    }

    val peephole = new global.closureElimination.PeepholeSimple

    val dcLiveClosures: mutable.Set[Symbol] = new mutable.HashSet[Symbol]

    def analyzeMethod(m: IMethod) {
      dieCodeDie(m, lnrzr)
      peephole(m) // TODO check whether peephole.liveness.toString() causes races, check also -Ylog
    }

    def dieCodeDie(m: IMethod, lnrzr: Linearizer) {
      assert(m.hasCode, m)
      log("dead code elimination on " + m);

      val rdef = new reachingDefinitions.ReachingDefinitionsAnalysis(lnrzr);

      /** Use-def chain: give the reaching definitions at the beginning of given instruction. */
      val defs: mutable.Map[(BasicBlock, Int), immutable.Set[rdef.lattice.Definition]] = mutable.HashMap.empty

      /** Useful instructions which have not been scanned yet. */
      val worklist: mutable.Set[(BasicBlock, Int)] = new mutable.LinkedHashSet

      /** which instructions have been marked as useful? */
      val useful: mutable.Map[BasicBlock, mutable.BitSet] = mutable.Map.empty

      /** Map instructions that have a drop on some control path, to that DROP instruction. */
      val dropOf: mutable.Map[(BasicBlock, Int), List[(BasicBlock, Int)]] = mutable.Map.empty

      m.code.blocks.clear()
      m.code.blocks ++= lnrzr.linearize(m)
      collectRDef(m, rdef, defs, worklist, useful, dropOf)
      mark(lnrzr, m, rdef, defs, worklist, useful, dropOf)
      /** local variables accessed at least once */
      val accessedLocals: List[Local] = (sweep(lnrzr, m, rdef, useful) ::: (m.params.reverse)).distinct
      if (m.locals diff accessedLocals nonEmpty) {
        log("Removed dead locals: " + (m.locals diff accessedLocals))
        m.locals = accessedLocals.reverse
      }
    }

    /** collect reaching definitions and initial useful instructions for this method. */
    def collectRDef(m       : IMethod,
                    rdef    : reachingDefinitions.ReachingDefinitionsAnalysis,
                    defs    : mutable.Map[(BasicBlock, Int), immutable.Set[reachingDefinitions.rdefLattice.Definition]],
                    worklist: mutable.Set[(BasicBlock, Int)],
                    useful  : mutable.Map[BasicBlock, mutable.BitSet],
                    dropOf  : mutable.Map[(BasicBlock, Int), List[(BasicBlock, Int)]]
                   ): Unit = {
      assert(defs     isEmpty,     defs)
      assert(worklist isEmpty, worklist)
      assert(useful   isEmpty,   useful)

      rdef.init(m);
      rdef.run;

      m foreachBlock { bb =>
        useful(bb) = new mutable.BitSet(bb.size)
        var rd = rdef.in(bb);
        for (Pair(i, idx) <- bb.toList.zipWithIndex) {
          i match {
            case LOAD_LOCAL(l) =>
              defs += Pair(((bb, idx)), rd.vars)
              // Console.println(i + ": " + (bb, idx) + " rd: " + rd + " and having: " + defs)
            case RETURN(_) | JUMP(_) | CJUMP(_, _, _, _) | CZJUMP(_, _, _, _) | STORE_FIELD(_, _) |
                 THROW(_)   | LOAD_ARRAY_ITEM(_) | STORE_ARRAY_ITEM(_) | SCOPE_ENTER(_) | SCOPE_EXIT(_) | STORE_THIS(_) |
                 LOAD_EXCEPTION(_) | SWITCH(_, _) | MONITOR_ENTER() | MONITOR_EXIT() => worklist += ((bb, idx))
            case CALL_METHOD(m1, _) if isSideEffecting(m1) => worklist += ((bb, idx)); log("marking " + m1)
            case CALL_METHOD(m1, SuperCall(_)) =>
              worklist += ((bb, idx)) // super calls to constructor
            case DROP(_) =>
              val necessary = rdef.findDefs(bb, idx, 1) exists { p =>
                val (bb1, idx1) = p
                bb1(idx1) match {
                  case CALL_METHOD(m1, _) if isSideEffecting(m1) => true
                  case LOAD_EXCEPTION(_) | DUP(_) | LOAD_MODULE(_) => true
                  case _ =>
                    dropOf((bb1, idx1)) = (bb,idx) :: dropOf.getOrElse((bb1, idx1), Nil)
                    // println("DROP is innessential: " + i + " because of: " + bb1(idx1) + " at " + bb1 + ":" + idx1)
                    false
                }
              }
              if (necessary) worklist += ((bb, idx))
            case _ => ()
          }
          rd = rdef.interpret(bb, idx, rd)
        }
      }
    }

    /** Mark useful instructions. Instructions in the worklist are each inspected and their
     *  dependencies are marked useful too, and added to the worklist.
     */
    def mark(lnrzr: Linearizer,
             m       : IMethod,
             rdef    : reachingDefinitions.ReachingDefinitionsAnalysis,
             defs    : mutable.Map[(BasicBlock, Int), immutable.Set[reachingDefinitions.rdefLattice.Definition]],
             worklist: mutable.Set[(BasicBlock, Int)],
             useful  : mutable.Map[BasicBlock, mutable.BitSet],
             dropOf  : mutable.Map[(BasicBlock, Int), List[(BasicBlock, Int)]]) {
      // log("Starting with worklist: " + worklist)
      while (!worklist.isEmpty) {
        val (bb, idx) = worklist.iterator.next
        worklist -= ((bb, idx))
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
              for ((l2, bb1, idx1) <- defs((bb, idx)) if l1 == l2; if !useful(bb1)(idx1)) {
                log("\tAdding " + bb1(idx1))
                worklist += ((bb1, idx1))
              }

            case nw @ NEW(REFERENCE(sym)) =>
              assert(nw.init ne null, "null new.init at: " + bb + ": " + idx + "(" + instr + ")")
              worklist += findInstruction(lnrzr, m, bb, nw.init)
              if (inliner.isClosureClass(sym)) {
                dcLiveClosures += sym
              }

            // it may be better to move static initializers from closures to
            // the enclosing class, to allow the optimizer to remove more closures.
            // right now, the only static fields in closures are created when caching
            // 'symbol literals.
            case LOAD_FIELD(sym, true) if inliner.isClosureClass(sym.owner) =>
              log("added closure class for field " + sym)
              dcLiveClosures += sym.owner

            case LOAD_EXCEPTION(_) =>
              ()

            case _ =>
              val icon = global synchronized { instr.consumed }
              for ((bb1, idx1) <- rdef.findDefs(bb, idx, icon) if !useful(bb1)(idx1)) {
                log("\tAdding " + bb1(idx1))
                worklist += ((bb1, idx1))
              }
          }
        }
      }
    }

    def sweep(lnrzr : Linearizer,
              m     : IMethod,
              rdef  : reachingDefinitions.ReachingDefinitionsAnalysis,
              useful: mutable.Map[BasicBlock, mutable.BitSet]): List[Local] = {
      val compensations = computeCompensations(lnrzr, m, rdef, useful)

      var localUsages: List[Local] = Nil

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
              case LOAD_LOCAL(l) if !l.arg =>
                localUsages = l :: localUsages
              case STORE_LOCAL(l) if !l.arg =>
                localUsages = l :: localUsages
              case _ => ()
            }
          } else {
            i match {
              case NEW(REFERENCE(sym)) =>
                log("skipped object creation: " + sym + "inside " + m)
              case _ => ()
            }
            debuglog("Skipped: bb_" + bb + ": " + idx + "( " + i + ")")
          }
        }

        if (bb.nonEmpty) bb.close
        else log("empty block encountered")
      }

      localUsages
    }

    private def computeCompensations(lnrzr : Linearizer,
                                     m     : IMethod,
                                     rdef  : reachingDefinitions.ReachingDefinitionsAnalysis,
                                     useful: mutable.Map[BasicBlock, mutable.BitSet]
                                    ): mutable.Map[(BasicBlock, Int), List[Instruction]] = {
      val compensations: mutable.Map[(BasicBlock, Int), List[Instruction]] = new mutable.HashMap

      m foreachBlock { bb =>
        assert(bb.closed, "Open block in computeCompensations")
        for ((i, idx) <- bb.toList.zipWithIndex) {
          if (!useful(bb)(idx)) {
            val ict = global synchronized { i.consumedTypes }
            for ((consumedType, depth) <- ict.reverse.zipWithIndex) {
              log("Finding definitions of: " + i + "\n\t" + consumedType + " at depth: " + depth)
              val defs = rdef.findDefs(bb, idx, 1, depth)
              for (d <- defs) {
                val (bb, idx) = d
                bb(idx) match {
                  case DUP(_) if idx > 0 =>
                    bb(idx - 1) match {
                      case nw @ NEW(_) =>
                        val init = findInstruction(lnrzr, m, bb, nw.init)
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

    private def findInstruction(lnrzr: Linearizer, m: IMethod, bb: BasicBlock, i: Instruction): (BasicBlock, Int) = {
      for (b <- lnrzr.linearizeAt(m, bb)) {
        val idx = b.toList indexWhere (_ eq i)
        if (idx != -1)
          return (b, idx)
      }
      abort("could not find init in: " + m)
    }

    private def isPure(sym: Symbol) = (
         (sym.isGetter && sym.isEffectivelyFinal && !sym.isLazy)
      || (sym.isPrimaryConstructor && (sym.enclosingPackage == RuntimePackage || inliner.isClosureClass(sym.owner)))
    )
    /** Is 'sym' a side-effecting method? TODO: proper analysis.  */
    private def isSideEffecting(sym: Symbol) = global synchronized { !isPure(sym) }

  } /* DeadCode */
}