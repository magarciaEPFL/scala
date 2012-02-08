/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Iulian Dragos
 */


package scala.tools.nsc
package backend.opt

import scala.collection.mutable
import scala.tools.nsc.symtab._
import scala.tools.nsc.util.{ NoSourceFile }
import java.util.concurrent.PriorityBlockingQueue

/**
 *  @author Iulian Dragos
 */
abstract class Inliners extends SubComponent {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions.{
    NullClass, NothingClass, ObjectClass,
    PredefModule, RuntimePackage, ScalaInlineClass, ScalaNoInlineClass,
    isFunctionType
  }

  val phaseName = "inliner"

  /* A warning threshold */
  private final val MAX_INLINE_MILLIS = 2000

  /** The maximum size in basic blocks of methods considered for inlining. */
  final val MAX_INLINE_SIZE = 16

  /** Maximum loop iterations. */
  final val MAX_INLINE_RETRY = 15

  /** Small method size (in blocks) */
  val SMALL_METHOD_SIZE = 1

  /** Create a new phase */
  override def newPhase(p: Phase) = new InliningPhase(p)

  // ------------------------------------------------------------------------------------------
  // Single entry point for locking purposes during inlining
  // ------------------------------------------------------------------------------------------

  @inline private final def gLocked[T](f: => T): T = { global synchronized { f } }

  // ------------------------------------------------------------------------------------------
  // thread-safe logging
  // ------------------------------------------------------------------------------------------

  var isLogActive      = false // actually initialized in InliningPhase
  var isDebugLogActive = false // actually initialized in InliningPhase
  @inline final def debuglog(msg: => String) { if(isDebugLogActive) { gLocked { global.debuglog(msg) } } }
  @inline final def log     (msg: => AnyRef) { if(isLogActive)      { gLocked { global.log(msg)      } } }
  @inline final def warning (pos: Position, msg: => String) { gLocked { reporter.warning(pos, msg) } }

  // ------------------------------------------------------------------------------------------
  // inspector methods also used from TypeFlowAnalysis
  // ------------------------------------------------------------------------------------------

  def isBottomType(sym: Symbol)    = sym == NullClass || sym == NothingClass
  def posToStr(pos: util.Position) = if (pos.isDefined) pos.point.toString else "<nopos>"

  /** Is the given class a closure? */
  def isClosureClass(cls: Symbol): Boolean =
    cls.isFinal && cls.isSynthetic && !cls.isModuleClass && cls.isAnonymousFunction

  //  TODO now that Inliner runs faster we could consider additional "monadic methods" (in the limit, all those taking a closure as last arg)
  //  Any "monadic method" occurring in a given caller C that is not `isMonadicMethod()` will prevent CloseElim from eliminating
  //  any anonymous-closure-class any whose instances are given as argument to invocations of C.
  def isMonadicMethod(sym: Symbol) = {
    nme.unspecializedName(sym.name) match {
      case nme.foreach | nme.filter | nme.withFilter | nme.map | nme.flatMap => true
      case _                                                                 => false
    }
  }

  /** Look up implementation of method 'sym in 'clazz'.
   */
  def lookupImplFor(sym: Symbol, clazz: Symbol): Symbol = gLocked {
    // TODO: verify that clazz.superClass is equivalent here to clazz.tpe.parents(0).typeSymbol (.tpe vs .info)
    def needsLookup = (
         (clazz != NoSymbol)
      && (clazz != sym.owner)
      && !sym.isEffectivelyFinal
      && clazz.isEffectivelyFinal
    )
    def lookup(clazz: Symbol): Symbol = {
      // println("\t\tlooking up " + meth + " in " + clazz.fullName + " meth.owner = " + meth.owner)
      if (sym.owner == clazz || isBottomType(clazz)) sym
      else sym.overridingSymbol(clazz) match {
        case NoSymbol  => if (sym.owner.isTrait) sym else lookup(clazz.superClass)
        case imp       => imp
      }
    }
    if (needsLookup) {
      val concreteMethod = lookup(clazz)
      debuglog("\tlooked up method: " + concreteMethod.fullName)

      concreteMethod
    }
    else sym
  }

  // ------------------------------------------------------------------------------------------
  // thread-pool-wide cache of @inline vs @noinline status of methods
  // ------------------------------------------------------------------------------------------

  private val inlineAnnCache = new _root_.java.util.concurrent.ConcurrentHashMap[Symbol, Int] // value encodes whether @inline (+1), @noinline (-1), or none of the previous (0).

  private def addToInlineCache(sym: Symbol): Int = {
    var res = 0
    gLocked {
      if     (sym hasAnnotation ScalaInlineClass)   res =  1
      else if(sym hasAnnotation ScalaNoInlineClass) res = -1
    }
    inlineAnnCache.put(sym, res)

    res
  }

  def hasInline(sym: Symbol): Boolean   = {
    val res =
      if(!inlineAnnCache.containsKey(sym)) addToInlineCache(sym)
      else                                 inlineAnnCache.get(sym)

    res == 1
  }

  def hasNoInline(sym: Symbol): Boolean   = {
    val res =
      if(!inlineAnnCache.containsKey(sym)) addToInlineCache(sym)
      else                                 inlineAnnCache.get(sym)

    res == -1
  }

  // ------------------------------------------------------------------------------------------
  // thread-pool-wide cache of method known to be never inlinale
  // ------------------------------------------------------------------------------------------

  // `knownNever` needs be cleared only at the very end of the inlining phase (unlike `tfa.knownUnsafe` and `tfa.knownSafe`)
  val knownNever = new _root_.java.util.concurrent.ConcurrentHashMap[Symbol, Int] // used as a set: values are dummies

  // ------------------------------------------------------------------------------------------
  // mechanism for multiple readers and multiple writers of the basic blocks owned by different IMethod s
  // ------------------------------------------------------------------------------------------

  /* (value, key) denotes (method symbol, N) where N encodes:
   *    -1 : the method is write-locked (by a single writer)
   *     0 : the method has no locks whatsoever on it
   *   > 0 : number of readers each holding a read-lock
   * */
  private val rwLocks  = new _root_.java.util.concurrent.ConcurrentHashMap[Symbol, _root_.java.util.concurrent.atomic.AtomicInteger]

  private def canWriteLock(msym: Symbol): Boolean = {
    var ai   = new _root_.java.util.concurrent.atomic.AtomicInteger(0)
    val prev = rwLocks.putIfAbsent(msym, ai)
    if(prev != null) { ai = prev}
    ai.compareAndSet(0, -1)
  }

  private def canReadLock(msym: Symbol): Boolean = {
    var ai   = new _root_.java.util.concurrent.atomic.AtomicInteger(0)
    val prev = rwLocks.putIfAbsent(msym, ai)
    if(prev != null) { ai = prev }
    var success = false
    val cnt = ai.get()
    if(cnt >= 0) {
      success = ai.compareAndSet(cnt, cnt + 1)
    }
    success
  }

  private def releaseWriteLock(msym: Symbol) {
    val ai = rwLocks.get(msym)
    val isOK = ai.compareAndSet(-1, 0)
    assert(isOK)
  }

  private def releaseReadLock(msym: Symbol) {
    val ai  = rwLocks.get(msym)
    var success = false
    while(!success) {
      val cnt = ai.get()
      success = ai.compareAndSet(cnt, cnt - 1)
      assert(cnt > 0)
    }
  }

  // ------------------------------------------------------------------------------------------
  // thread-pool-wide cache of type-flow analyses of external methods that have been marked as @inline
  // ------------------------------------------------------------------------------------------

  val recentTFAs = new _root_.java.util.concurrent.ConcurrentHashMap[Symbol, Tuple2[Boolean, analysis.MTFACoarse]]
  def getRecentTFA(incm: IMethod): (Boolean, analysis.MTFACoarse) = {

      def containsRETURN(blocks: List[BasicBlock]) = blocks exists { bb => bb.lastInstruction.isInstanceOf[RETURN] }

    val opt = recentTFAs.get(incm.symbol)
    if(opt != null) {
      // FYI val cachedBBs = opt._2.in.keySet
      // FYI assert(incm.blocks.toSet == cachedBBs)
      // incm.code.touched plays no role here
      return opt
    }

    val hasRETURN = containsRETURN(incm.code.blocksList) || (incm.exh exists { eh => containsRETURN(eh.blocks) })
    var a: analysis.MTFACoarse = null
    if(hasRETURN) { a = new analysis.MTFACoarse(incm); a.run } // TODO use MTFACoarse

    if(hasInline(incm.symbol)) { recentTFAs.put(incm.symbol, (hasRETURN, a)) }

    (hasRETURN, a)
  }

  // ------------------------------------------------------------------------------------------
  // job priority queue
  // ------------------------------------------------------------------------------------------

  private class  QElem(val im: IMethod, val blockCount: Int, val pastAttempts: Int)
  private object poison extends QElem(null, 0, -1)

  private val MAX_THREADS = scala.math.min(
    16,
    _root_.java.lang.Runtime.getRuntime().availableProcessors()
  )

  private val oldestlast = new _root_.java.util.Comparator[QElem] {
    override def compare(a: QElem, b: QElem) = {
      if     (a eq poison)  1
      else if(b eq poison) -1 // ok not to check for both being poison
      else {
        a.pastAttempts - b.pastAttempts
      }
    }
  }

  private val largemethodsfirst = new _root_.java.util.Comparator[QElem] {
    override def compare(a: QElem, b: QElem) = {
      if     (a eq poison)  1
      else if(b eq poison) -1 // ok not to check for both being poison
      else {
        a.blockCount - b.blockCount
      }
    }
  }

  private var q         = new _root_.java.util.concurrent.PriorityBlockingQueue[QElem](100, largemethodsfirst)
  private var spillover = new _root_.java.util.concurrent.PriorityBlockingQueue[QElem](100, largemethodsfirst)
  // private val q = new _root_.java.util.concurrent.LinkedBlockingQueue[QElem]

  // ------------------------------------------------------------------------------------------
  // Worker
  // ------------------------------------------------------------------------------------------

  var stats: Boolean     = false // actually initialized in InliningPhase
  private val statMillis = new _root_.java.util.concurrent.ConcurrentHashMap[Symbol, Int]
  private val statThread = new _root_.java.util.concurrent.ConcurrentHashMap[Symbol, Long]

  class InlinerTask extends _root_.java.lang.Runnable() {

    val inliner = new Inliner()

    def run() {
      var j: QElem = null
      while(j ne poison) {
        j = q.take()
        if (j ne poison) {
          if(stats) timed(j.im.symbol, inliner.analyzeMethod(j))
          else inliner.analyzeMethod(j)
        }
      }
      inliner.tfa.clearCaches()
    }

    private def timed[T](msym: Symbol, body: => T): T = {
      val t1  = System.currentTimeMillis()
      val res = body
      val t2  = System.currentTimeMillis()
      val elapsed = (t2 - t1).toInt
      statMillis.put(msym, elapsed)
      statThread.put(msym, Thread.currentThread().getId())

      res
    }
  }

  /** The Inlining phase.
   */
  class InliningPhase(prev: Phase) extends ICodePhase(prev) {
    def name = phaseName

    isLogActive      = (settings.log.containsPhase(this))
    isDebugLogActive = (isLogActive && settings.debug.value)
    stats            = (isLogActive && opt.printStats)

    override def apply(cls: IClass) {
      if (settings.inline.value) {
        val ms = cls.methods filterNot { _.symbol.isConstructor }
        ms foreach { im =>
          if(hasInline(im.symbol)) {
            log("Not inlining into " + im.symbol.originalName.decode + " because it is marked @inline.")
          } else if(im.hasCode && !im.symbol.isBridge) {
            q put new QElem(im, im.code.blockCount, 0)
          }
        }
      }
    }

    private def allLocksFreed: Boolean = {
      val iter = rwLocks.entrySet().iterator()
      while(iter.hasNext) {
        val e = iter.next
        if(e.getValue().get() != 0) { return false }
      }
      true
    }

    override def run() {
      try {
        super.run() // not nice: unitTimings will be artificially low
        var anotherRound = false
        do {
          anotherRound = false
          val exec = _root_.java.util.concurrent.Executors.newFixedThreadPool(MAX_THREADS)
          val workers = for(i <- 1 to MAX_THREADS) yield { val t = new InlinerTask; exec.execute(t); t }
          workers foreach { w => q put poison }
          exec.shutdown()
          while(!exec.isTerminated) { exec.awaitTermination(1, _root_.java.util.concurrent.TimeUnit.MILLISECONDS) }
          // TODO assert(q.isEmpty)
          if(!spillover.isEmpty) {
            anotherRound = true
            q = spillover
            spillover = new _root_.java.util.concurrent.PriorityBlockingQueue[QElem](100, largemethodsfirst)
          }
        } while (anotherRound)

        // TODO assert(q.isEmpty)
        assert(allLocksFreed)

        if(stats) {
          val iter = statMillis.entrySet().iterator
          while(iter.hasNext) {
            val e    = iter.next
            val msym = e.getKey()
            inform("[inliner][par] elapsed: %9d ms".format(e.getValue()) +
                   " , thread: %6d".format(statThread.get(msym)) +
                   " , method: " + msym.fullName)
           }
        }
      } finally {
        statMillis.clear()
        statThread.clear()
        recentTFAs.clear
        inlineAnnCache.clear()
        knownNever.clear()
      }
    }

  } // end of class InliningPhase

  /**
   * Simple inliner.
   */
  class Inliner {
    object NonPublicRefs extends Enumeration {
      val Private, Protected, Public = Value
    }
    import NonPublicRefs._

    val tfa   = new analysis.MTFAGrowable(knownNever)
    tfa.stat  = global.opt.printStats
    val staleOut      = new mutable.ListBuffer[BasicBlock]
    val splicedBlocks = mutable.Set.empty[BasicBlock]
    val staleIn       = mutable.Set.empty[BasicBlock]

    val lnrzr: Linearizer = settings.Xlinearizer.value match {
      case "rpo"    => new ReversePostOrderLinearizer()
      case "dfs"    => new DepthFirstLinerizer()
      case "normal" => new NormalLinearizer()
      case "dump"   => new DumpLinearizer()
      case x        => global.abort("Unknown linearizer: " + x)
    }

    def analyzeMethod(workItem: QElem): Unit = {
      val m = workItem.im
      if(canWriteLock(m.symbol)) {
        try     analyzeMethod0(m)
        finally releaseWriteLock(m.symbol)
      } else {
        // resubmit m with priority one below its current (up to some threshold)
        if (workItem.pastAttempts < MAX_INLINE_RETRY) {
          spillover put new QElem(m, workItem.blockCount, workItem.pastAttempts + 1)
        }
      }
    }

    private def analyzeMethod0(m: IMethod): Unit = {
      val sizeBeforeInlining  = m.code.blockCount
      val instrBeforeInlining = m.code.instructionCount
      var retry = false
      var count = 0

      // fresh name counter
      val fresh = mutable.HashMap.empty[String, Int] withDefaultValue 0
      // how many times have we already inlined methods given by keys in `m`?
      val inlinedMethodCount = mutable.HashMap.empty[Symbol, Int] withDefaultValue 0

      val caller = gLocked { new IMethodInfo(m) } // we don't lock each RHSs of IMethodInfo's val, thus we have to lock while its constructor runs.

      def preInline(isFirstRound: Boolean): Int = {
        val inputBlocks = caller.m.linearizedBlocks(lnrzr)
        val callsites: Function1[BasicBlock, List[opcodes.CALL_METHOD]] = {
          if(isFirstRound) tfa.conclusives else tfa.knownBeforehand
        }
        inlineWithoutTFA(inputBlocks, callsites)
      }

      /**
       *  Inline straightforward callsites (those that can be inlined without a TFA).
       *
       *  To perform inlining, all we need to know is listed as formal params in `analyzeInc()`:
       *    - callsite and block containing it
       *    - actual (ie runtime) class of the receiver
       *    - actual (ie runtime) method being invoked
       *    - stack length just before the callsite (to check whether enough arguments have been pushed).
       *  The assert below lists the conditions under which "no TFA is needed"
       *  (the statically known receiver and method are both final, thus, at runtime they can't be any others than those).
       *
       */
      def inlineWithoutTFA(inputBlocks: Traversable[BasicBlock], callsites: Function1[BasicBlock, List[opcodes.CALL_METHOD]]): Int = {
        var inlineCount = 0
        import scala.util.control.Breaks._
        for(x <- inputBlocks; val easyCake = callsites(x); if easyCake.nonEmpty) { // TODO backport (single pass now instead of retries)
          breakable {
            for(ocm <- easyCake) {
              var receiver: Symbol       = NoSymbol
              var concreteMethod: Symbol = NoSymbol
              gLocked {
                receiver       = ocm.method.owner
                concreteMethod = ocm.method
                assert(concreteMethod.isEffectivelyFinal && receiver.isEffectivelyFinal)
              }
              if(analyzeInc(ocm, x, receiver, -1, concreteMethod)) {
                inlineCount += 1
                break
              }
            }
          }
        }

        inlineCount
      }

      /**
          Decides whether it's feasible and desirable to inline the body of the method given by `concreteMethod`
          at the program point given by `i` (a callsite). The boolean result indicates whether inlining was performed.

       */
      def analyzeInc(i: CALL_METHOD, bb: BasicBlock, receiver: Symbol, stackLength: Int, concreteMethod: Symbol): Boolean = {
        var inlined = false
        val msym = i.method

        def warnNoInline(reason: String) = {
          if (hasInline(msym) && !caller.isBridge)
            warning(i.pos, "Could not inline required method %s because %s.".format(msym.originalName.decode, reason))
        }

        def isAvailable = { gLocked { icodes available concreteMethod.enclClass } }

        gLocked {
          if (!isAvailable && shouldLoadImplFor(concreteMethod, receiver)) {
            // Until r22824 this line was:
            //   icodes.icode(concreteMethod.enclClass, true)
            //
            // Changing it to
            //   icodes.load(concreteMethod.enclClass)
            // was the proximate cause for SI-3882:
            //   error: Illegal index: 0 overlaps List((variable par1,LONG))
            //   error: Illegal index: 0 overlaps List((variable par1,LONG))
            icodes.load(concreteMethod.enclClass)
          }
        }

        def isCandidate = (
             isClosureClass(receiver)
          || concreteMethod.isEffectivelyFinal
          || receiver.isEffectivelyFinal
        )
        def isApply     = concreteMethod.name == nme.apply
        def isCountable = !(
             isClosureClass(receiver)
          || isApply
          || isMonadicMethod(concreteMethod)
          || gLocked { receiver.enclosingPackage == definitions.RuntimePackage }
        )   // only count non-closures

        debuglog("Treating " + i
              + "\n\treceiver: " + receiver
              + "\n\ticodes.available: " + isAvailable
              + "\n\tconcreteMethod.isEffectivelyFinal: " + concreteMethod.isEffectivelyFinal)

        if (isAvailable && isCandidate) {
          lookupIMethod(concreteMethod, receiver) match {
            case Some(callee) =>
              // isExternal implies no need to read-lock callee's symbol
              // val isExternal = gLocked { icodes.loaded.contains(callee.symbol.enclClass) }

              if( /* isExternal || */ canReadLock(callee.symbol)) {
                try {
                  val inc   = gLocked { new IMethodInfo(callee) }
                  val pair  = new CallerCalleeInfo(caller, inc, fresh, inlinedMethodCount)

                  if (pair isStampedForInlining stackLength) {
                    retry = true
                    inlined = true
                    if (isCountable) { count += 1 }
                    pair.doInline(bb, i)
                    if (!inc.inline || inc.isMonadic) { caller.inlinedCalls += 1 }
                    inlinedMethodCount(inc.sym) += 1
                    // The calls-private relation might have changed due to the inlining.
                    recentTFAs.remove(m.symbol)
                  }
                  else {
                    if (settings.debug.value) { pair logFailure stackLength }
                    warnNoInline(pair failureReason stackLength)
                  }
                } finally {
                  /* if(!isExternal) */ releaseReadLock(callee.symbol)
                }
              } else {
                // TODO add this block to a analyzeMethod0-local queue for bounded retry
              }

            case None =>
              warnNoInline("bytecode was not available")
              debuglog("could not find icode\n\treceiver: " + receiver + "\n\tmethod: " + concreteMethod)
          }
        } else {
          warnNoInline( if (!isAvailable) "bytecode was not available" else "it can be overridden" )
        }

        inlined
      }

      /* Pre-inlining consists in invoking the usual inlining subroutine with (receiver class, concrete method) pairs as input
       * where both method and receiver are final, which implies that the receiver computed via TFA will always match `concreteMethod.owner`.
       *
       * As with any invocation of `analyzeInc()` the inlining outcome is based on heuristics which favor inlining an isMonadicMethod before other methods.
       * That's why preInline() is invoked twice: any inlinings downplayed by the heuristics during the first round get an opportunity to rank higher during the second.
       *
       * As a whole, both `preInline()` invocations amount to priming the inlining process,
       * so that the first TFA run afterwards is able to gain more information as compared to a cold-start.
       */
      val totalPreInlines = {
        val firstRound = preInline(true)
        if(firstRound == 0) 0 else (firstRound + preInline(false))
      }
      staleOut.clear()
      splicedBlocks.clear()
      staleIn.clear()

      do {
        retry = false
        log("Analyzing " + m + " count " + count + " with " + caller.length + " blocks")

        /* it's important not to inline in unreachable basic blocks. linearizedBlocks() returns only reachable ones. */
        tfa.callerLin = caller.m.linearizedBlocks(lnrzr)
        tfa.reinit(m, staleOut.toList, splicedBlocks, staleIn)
        tfa.run
        staleOut.clear()
        splicedBlocks.clear()
        staleIn.clear()

        import scala.util.control.Breaks._
        for(bb <- tfa.callerLin; if tfa.preCandidates(bb)) {
          val cms = bb.toList collect { case cm : CALL_METHOD => cm }
          breakable {
            for (cm <- cms; if tfa.remainingCALLs.isDefinedAt(cm)) {
              val analysis.CallsiteInfo(_, receiver, stackLength, concreteMethod) = tfa.remainingCALLs(cm)
              if (analyzeInc(cm, bb, receiver, stackLength, concreteMethod)) {
                break
              }
            }
          }
        }

        /*
        if(splicedBlocks.nonEmpty) { TODO explore because this saves 8 sec
          // opportunistically perform straightforward inlinings before the next typeflow round
          val savedRetry = retry
          val savedStaleOut = staleOut.toSet; staleOut.clear()
          val savedStaleIn  = staleIn.toSet ; staleIn.clear()
          val howmany = inlineWithoutTFA(splicedBlocks, tfa.knownBeforehand)
          if(howmany > 0) println("inlineWithoutTFA: " + howmany);
          splicedBlocks ++= staleIn
          staleOut.clear(); staleOut ++= savedStaleOut;
          staleIn.clear();  staleIn  ++= savedStaleIn;
          retry = savedRetry
        }
        */

        if (tfa.stat)
          log(caller.fullName + " iterations: " + tfa.iterations + " (size: " + caller.length + ")")
      }
      while (retry && count < MAX_INLINE_RETRY)

      m.normalize
      if (sizeBeforeInlining > 0) {
        val instrAfterInlining = m.code.instructionCount
        val prefix = if ((instrAfterInlining > 2 * instrBeforeInlining) && (instrAfterInlining > 200)) " !! " else ""
        log(prefix + " %s blocks before inlining: %d (%d) after: %d (%d)".format(
          caller.fullName, sizeBeforeInlining, instrBeforeInlining, m.code.blockCount, instrAfterInlining))
      }
    }

    private def isHigherOrderMethod(sym: Symbol) = gLocked {
      sym.isMethod && atPhase(currentRun.erasurePhase.prev)(sym.info.paramTypes exists isFunctionType)
    }

    /** Should method 'sym' being called in 'receiver' be loaded from disk? */
    private def shouldLoadImplFor(sym: Symbol, receiver: Symbol): Boolean = {
      def alwaysLoad    = (receiver.enclosingPackage == RuntimePackage) || (receiver == PredefModule.moduleClass)
      def loadCondition = sym.isEffectivelyFinal && isMonadicMethod(sym) && isHigherOrderMethod(sym)

      val res = hasInline(sym) || alwaysLoad || loadCondition
      debuglog("shouldLoadImplFor: " + receiver + "." + sym + ": " + res)
      res
    }

    class IMethodInfo(val m: IMethod) {
      val sym           = m.symbol
      val name          = sym.name
      val fullName      = sym.fullName
      val owner         = sym.owner
      val minimumStack  = sym.info.paramTypes.length + 1

      val inline        = hasInline(sym)
      val noinline      = hasNoInline(sym)

      val isBridge      = sym.isBridge
      val isInClosure   = isClosureClass(owner)
      val isHigherOrder = isHigherOrderMethod(sym)
      val isMonadic     = isMonadicMethod(sym)

      def handlers      = m.exh
      def blocks        = m.blocks
      def locals        = m.locals
      def length        = blocks.length
      def openBlocks    = blocks filterNot (_.closed)
      def instructions  = m.code.instructions

      def isSmall       = (length <= SMALL_METHOD_SIZE) && blocks(0).length < 10
      def isLarge       = length > MAX_INLINE_SIZE
      def isRecursive   = m.recursive
      def hasHandlers   = handlers.nonEmpty
      def hasNonFinalizerHandler = handlers exists {
        case _: Finalizer => true
        case _            => false
      }

      // the number of inlined calls in 'm', used by 'shouldInline'
      var inlinedCalls = 0

      def addLocals(ls: List[Local])  = m.locals ++= ls
      def addLocal(l: Local)          = addLocals(List(l))
      def addHandlers(exhs: List[ExceptionHandler]) = m.exh = exhs ::: m.exh

      private var toBecomePublic: List[Symbol] = Nil

      lazy val accessNeeded: NonPublicRefs.Value = gLocked {

        def check(sym: Symbol, cond: Boolean) =
          if (cond) Private
          else if (sym.isProtected) Protected
          else Public

        def canMakePublic(f: Symbol): Boolean =
          (m.sourceFile ne NoSourceFile) && (f.isSynthetic || f.isParamAccessor) &&
          { toBecomePublic = f :: toBecomePublic; true }

        def checkField(f: Symbol)   = check(f, f.isPrivate && !canMakePublic(f))
        def checkSuper(n: Symbol)   = check(n, n.isPrivate || !n.isClassConstructor)
        def checkMethod(n: Symbol)  = check(n, n.isPrivate)

        def getAccess(i: Instruction) = i match {
          case CALL_METHOD(n, SuperCall(_)) => checkSuper(n)
          case CALL_METHOD(n, _)            => checkMethod(n)
          case LOAD_FIELD(f, _)             => checkField(f)
          case STORE_FIELD(f, _)            => checkField(f)
          case _                            => Public
        }

        toBecomePublic = Nil
        var seen = Public
        val iter = instructions.iterator
        while((seen ne Private) && iter.hasNext) {
          val i = iter.next()
          getAccess(i) match {
            case Private    => seen = Private ; log("instruction " + i + " requires private access.")
            case Protected  => seen = Protected
            case _          => ()
          }
        }

        seen
      }

      def doMakePublic(): Boolean = {
        for(f <- toBecomePublic) {
          debuglog("Making not-private symbol out of synthetic: " + f)
          f setNotFlag Flags.PRIVATE
        }
        toBecomePublic = Nil
        true
      }

    }

    class CallerCalleeInfo(val caller: IMethodInfo, val inc: IMethodInfo, fresh: mutable.Map[String, Int], inlinedMethodCount: collection.Map[Symbol, Int]) {
      def isLargeSum  = caller.length + inc.length - 1 > SMALL_METHOD_SIZE

      private def freshName(s: String): TermName = {
        fresh(s) += 1
        newTermName(s + fresh(s))
      }

      /** Inline 'inc' into 'caller' at the given block and instruction.
       */
      def doInline(block: BasicBlock, instr: CALL_METHOD) {

        staleOut += block

        tfa.remainingCALLs.remove(instr) // this bookkpeeping is done here and not in MTFAGrowable.reinit due to (1st) convenience and (2nd) necessity.
        tfa.isOnWatchlist.remove(instr)  // ditto

        val targetPos = instr.pos
        log("Inlining " + inc.m + " in " + caller.m + " at pos: " + posToStr(targetPos))

        def blockEmit(i: Instruction) = block.emit(i, targetPos)
        def newLocal(baseName: String, kind: TypeKind) =
          gLocked { new Local(caller.sym.newVariable(freshName(baseName), targetPos), kind, false) }

        val (hasRETURN, a) = getRecentTFA(inc.m)

        /* The exception handlers that are active at the current block. */
        val activeHandlers = caller.handlers filter (_ covered block)

        /* Map 'original' blocks to the ones inlined in the caller. */
        val inlinedBlock: mutable.Map[BasicBlock, BasicBlock] = new mutable.HashMap

        val varsInScope: mutable.Set[Local] = mutable.HashSet() ++= block.varsInScope

        /** Side effects varsInScope when it sees SCOPE_ENTERs. */
        def instrBeforeFilter(i: Instruction): Boolean = {
          i match { case SCOPE_ENTER(l) => varsInScope += l ; case _ => () }
          i ne instr
        }
        val instrBefore = block.toList takeWhile instrBeforeFilter
        val instrAfter  = block.toList drop (instrBefore.length + 1)

        assert(!instrAfter.isEmpty, "CALL_METHOD cannot be the last instruction in block!")

        // store the '$this' into the special local
        val inlinedThis = newLocal("$inlThis", REFERENCE(ObjectClass))

        /** buffer for the returned value */
        val retVal =
          gLocked {
            inc.m.returnType match {
              case UNIT  => null
              case x     => newLocal("$retVal", x)
            }
          }

        val inlinedLocals = mutable.HashMap.empty[Local, Local]

        /** Add a new block in the current context. */
        def newBlock() = {
          val b = caller.m.code.newBlock
          activeHandlers foreach (_ addCoveredBlock b)
          if (retVal ne null) b.varsInScope += retVal
          b.varsInScope  += inlinedThis
          b.varsInScope ++= varsInScope
          b
        }

        def translateExh(e: ExceptionHandler) = {
          val handler: ExceptionHandler = e.dup
          handler.covered = handler.covered map inlinedBlock
          handler setStartBlock inlinedBlock(e.startBlock)
          handler
        }

        /** alfa-rename `l` in caller's context. */
        def dupLocal(l: Local): Local = { // rather than locking here, we lock its single invoker
          val sym = caller.sym.newVariable(freshName(l.sym.name.toString), l.sym.pos)
          // sym.setInfo(l.sym.tpe)
          val dupped = new Local(sym, l.kind, false)
          inlinedLocals(l) = dupped
          dupped
        }

        val afterBlock = newBlock()

        /** Map from nw.init instructions to their matching NEW call */
        val pending: mutable.Map[Instruction, NEW] = new mutable.HashMap

        /** Map an instruction from the callee to one suitable for the caller. */
        def map(i: Instruction): Instruction = {
          def assertLocal(l: Local) = {
            assert(caller.locals contains l, "Could not find local '" + l + "' in locals, nor in inlinedLocals: " + inlinedLocals)
            i
          }
          def isInlined(l: Local) = inlinedLocals isDefinedAt l

          val newInstr = i match {
            case THIS(clasz)                    => LOAD_LOCAL(inlinedThis)
            case STORE_THIS(_)                  => STORE_LOCAL(inlinedThis)
            case JUMP(whereto)                  => JUMP(inlinedBlock(whereto))
            case CJUMP(succ, fail, cond, kind)  => CJUMP(inlinedBlock(succ), inlinedBlock(fail), cond, kind)
            case CZJUMP(succ, fail, cond, kind) => CZJUMP(inlinedBlock(succ), inlinedBlock(fail), cond, kind)
            case SWITCH(tags, labels)           => SWITCH(tags, labels map inlinedBlock)
            case RETURN(_)                      => JUMP(afterBlock)
            case LOAD_LOCAL(l) if isInlined(l)  => LOAD_LOCAL(inlinedLocals(l))
            case STORE_LOCAL(l) if isInlined(l) => STORE_LOCAL(inlinedLocals(l))
            case LOAD_LOCAL(l)                  => assertLocal(l)
            case STORE_LOCAL(l)                 => assertLocal(l)
            case SCOPE_ENTER(l) if isInlined(l) => SCOPE_ENTER(inlinedLocals(l))
            case SCOPE_EXIT(l) if isInlined(l)  => SCOPE_EXIT(inlinedLocals(l))

            case nw @ NEW(sym) =>
              val r = NEW(sym)
              pending(nw.init) = r
              r

            case CALL_METHOD(meth, Static(true)) if meth.isClassConstructor =>
              CALL_METHOD(meth, Static(true))

            case _ => i.clone()
          }
          // check any pending NEW's
          pending remove i foreach (_.init = newInstr.asInstanceOf[CALL_METHOD])
          newInstr
        }

        gLocked { caller addLocals (inc.locals map dupLocal) }
        caller addLocal inlinedThis

        if (retVal ne null)
          caller addLocal retVal

        inc.m foreachBlock { b =>
          inlinedBlock += (b -> newBlock())
          inlinedBlock(b).varsInScope ++= (b.varsInScope map inlinedLocals)
        }

        // re-emit the instructions before the call
        block.open
        block.clear
        block emit instrBefore

        // store the arguments into special locals
        inc.m.params.reverse foreach (p => blockEmit(STORE_LOCAL(inlinedLocals(p))))
        blockEmit(STORE_LOCAL(inlinedThis))

        // jump to the start block of the callee
        blockEmit(JUMP(inlinedBlock(inc.m.startBlock)))
        block.close

        // duplicate the other blocks in the callee
        val calleeLin = inc.m.linearizedBlocks(lnrzr)
        calleeLin foreach { bb =>
          var info = if(hasRETURN) (a in bb) else null
          def emitInlined(i: Instruction) = inlinedBlock(bb).emit(i, targetPos)
          def emitDrops(toDrop: Int)      = info.stack.types drop toDrop foreach (t => emitInlined(DROP(t)))

          for (i <- bb) {
            i match {
              case RETURN(UNIT) => emitDrops(0)
              case RETURN(kind) =>
                if (info.stack.length > 1) {
                  emitInlined(STORE_LOCAL(retVal))
                  emitDrops(1)
                  emitInlined(LOAD_LOCAL(retVal))
                }
              case _            => ()
            }
            emitInlined(map(i))
            info = if(hasRETURN) a.interpret(info, i) else null
          }
          inlinedBlock(bb).close
        }

        afterBlock emit instrAfter
        afterBlock.close

        staleIn        += afterBlock
        splicedBlocks ++= (calleeLin map inlinedBlock)

        // add exception handlers of the callee
        caller addHandlers (inc.handlers map translateExh)
        assert(pending.isEmpty, "Pending NEW elements: " + pending)
        if (settings.debug.value) icodes.checkValid(caller.m)
      }

      def isStampedForInlining(stackLength: Int) =
        !sameSymbols && inc.m.hasCode && shouldInline && isSafeToInline(stackLength) &&
        inc.doMakePublic() // isSafeToInline(stack) is invoked a few times,
        // however doMakePublic() should be invoked just once (here) if isSafeToInline(stack) succeeds.
        // Because doMakePublic() is side-effecting.

      def logFailure(stackLength: Int) = log(
        """|inline failed for %s:
           |  pair.sameSymbols: %s
           |  inc.numInlined < 2: %s
           |  inc.m.hasCode: %s
           |  isSafeToInline: %s
           |  shouldInline: %s
        """.stripMargin.format(
          inc.m, sameSymbols, inlinedMethodCount(inc.sym) < 2,
          inc.m.hasCode, isSafeToInline(stackLength), shouldInline
        )
      )

      def failureReason(stackLength: Int) =
        if (!inc.m.hasCode) "bytecode was unavailable"
        else if (!isSafeToInline(stackLength)) "it is unsafe (target may reference private fields)"
        else "of a bug (run with -Ylog:inline -Ydebug for more information)"

      def canAccess(level: NonPublicRefs.Value) = level match {
        case Private    => caller.owner == inc.owner
        case Protected  => caller.owner.tpe <:< inc.owner.tpe
        case Public     => true
      }
      private def sameSymbols = caller.sym == inc.sym

      /** A method is safe to inline when:
       *    - it does not contain calls to private methods when called from another class
       *    - it is not inlined into a position with non-empty stack,
       *      while having a top-level finalizer (see liftedTry problem)
       *    - it is not recursive
       * Note:
       *    - synthetic private members are made public in this pass.
       */
      def isSafeToInline(stackLength: Int): Boolean = {

        if(tfa.blackballed(inc.sym)) { return false } // TODO backport
        if(tfa.knownSafe(inc.sym))   { return true  }

        if(helperIsSafeToInline(stackLength)) {
          tfa.knownSafe   += inc.sym; true
        } else {
          tfa.knownUnsafe += inc.sym; false
        }
      }

      private def helperIsSafeToInline(stackLength: Int): Boolean = {

        if (!inc.m.hasCode || inc.isRecursive) { return false }

        if(!inc.openBlocks.isEmpty) {
          // Avoiding crashing the compiler if there are open blocks.
          warning(inc.sym.pos,
            "Encountered one or more open blocks in isSafeToInline: this indicates a bug in the optimizer!\n" +
            "  caller = " + caller.m + ", callee = " + inc.m)
          return false
        }

        val isIllegalStack = (stackLength > inc.minimumStack && inc.hasNonFinalizerHandler)
        if(isIllegalStack) { debuglog("method " + inc.sym + " is used on a non-empty stack with finalizer.") }

        !isIllegalStack && canAccess(inc.accessNeeded)

      }

      /** Decide whether to inline or not. Heuristics:
       *   - it's bad to make the caller larger (> SMALL_METHOD_SIZE) if it was small
       *   - it's bad to inline large methods
       *   - it's good to inline higher order functions
       *   - it's good to inline closures functions.
       *   - it's bad (useless) to inline inside bridge methods
       */
      private def neverInline   = {
        (!inc.m.hasCode || inc.noinline || inc.isRecursive) && { knownNever.put(inc.m.symbol, 0); true } // TODO backport added inc.isRecursive as rule-out criterium
      }
      private def alwaysInline  = inc.inline

      def shouldInline: Boolean = !neverInline && (alwaysInline || {
        debuglog("shouldInline: " + caller.m + " with " + inc.m)

        var score = 0

        // better not inline inside closures, but hope that the closure itself is repeatedly inlined
        if (caller.isInClosure)           score -= 2
        else if (caller.inlinedCalls < 1) score -= 1 // only monadic methods can trigger the first inline

        if (inc.isSmall) score += 1;
        if (inc.isLarge) score -= 1;
        if (caller.isSmall && isLargeSum) {
          score -= 1
          debuglog("shouldInline: score decreased to " + score + " because small " + caller + " would become large")
        }

        if (inc.isMonadic)          score += 3
        else if (inc.isHigherOrder) score += 1

        if (inc.isInClosure)                 score += 2;
        if (inlinedMethodCount(inc.sym) > 2) score -= 2;

        log("shouldInline(" + inc.m + ") score: " + score)

        score > 0
      })
    }

    def lookupIMethod(meth: Symbol, receiver: Symbol): Option[IMethod] = gLocked {
      def tryParent(sym: Symbol) = icodes icode sym flatMap (_ lookupMethod meth)

      receiver.info.baseClasses.iterator map tryParent find (_.isDefined) flatten
    }
  } /* class Inliner */
} /* class Inliners */
