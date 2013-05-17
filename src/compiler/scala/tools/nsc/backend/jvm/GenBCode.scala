/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala
package tools.nsc
package backend
package jvm

import scala.collection.{ mutable, immutable }

import scala.tools.asm
import asm.tree.{FieldNode, MethodInsnNode, MethodNode}

/*
 *  Prepare in-memory representations of classfiles using the ASM Tree API, and serialize them to disk.
 *  Plain, mirror, and bean classes are built respectively by PlainClassBuilder, JMirrorBuilder, and JBeanInfoBuilder.
 *
 *  Three pipelines are at work, each taking work items from a queue dedicated to that pipeline:
 *
 *  (There's another pipeline so to speak, the one that populates queue-1 by traversing a CompilationUnit until ClassDefs are found,
 *   but the "interesting" pipelines are the ones described below)
 *
 *    (1) In the first queue, an item consists of a ClassDef along with its arrival position.
 *        This position is needed at the time classfiles are serialized to disk,
 *        so as to emit classfiles in the same order CleanUp handed them over.
 *        As a result, two runs of the compiler on the same files produce jars that are identical on a byte basis.
 *        See `ant test.stability`
 *
 *    (2) The second queue contains items where a ClassDef has been lowered into:
 *          (a) an optional mirror class,
 *          (b) a plain class, and
 *          (c) an optional bean class.
 *
 *        Pipeline 1
 *        ----------
 *
 *        The processing that takes place between queues 1 and 2 relies on typer, and thus has to be performed by a single thread.
 *        The thread in question is different from the main thread, for reasons that will become apparent below.
 *        As long as all operations on typer are carried out under a single thread (not necessarily the main thread), everything is fine.
 *
 *        Rather than performing all the work involved in lowering a ClassDef,
 *        pipeline-1 leaves in general for later those operations that don't require typer.
 *        All the can-multi-thread operations that pipeline-2 performs can also run during pipeline-1, in fact some of them do.
 *        In contrast, typer operations can't be performed by pipeline-2.
 *        pipeline-2 consists of MAX_THREADS worker threads running concurrently.
 *
 *        Pipeline 2
 *        ----------
 *
 *        The operations that a worker thread of pipeline-2 can perform are those that rely only on the following abstractions:
 *          - BType:     a typer-independent representation of a JVM-level type,
 *          - Tracked:   a bundle of a BType B, its superclass (as a BType), and B's interfaces (as BTypes).
 *          - exemplars: a concurrent map to obtain a Tracked structure using an internal class name as key.
 *          - the tree-based representation of classfiles provided by the ASM Tree API.
 *        For example:
 *          - it's possible to determine whether a BType conforms to another without resorting to typer.
 *          - `CClassWriter.getCommonSuperclass()` is thread-reentrant (therefore, it accesses only thread-reentrant functionality).
 *             This befits the way pipelin-2 works, because `MethodNode.visitMaxs()` invokes `getCommonSuperclass()` on different method nodes,
 *             and each of these activations accesses typer-independent structures (exemplars, Tracked) to compute its answer.
 *
 *        A pipeline-2 worker performs intra-method optimizations on the ASM tree.
 *        Briefly, `Worker2.visit()` instantiates a `BCodeOpt.BCodeCleanser` to perform those optimizations.
 *
 *    (3) The third queue contains items ready for serialization.
 *        It's a priority queue that follows the original arrival order,
 *        so as to emit identical jars on repeated compilation of the same sources.
 *
 *        Pipeline 3
 *        ----------
 *
 *        This pipeline consist of just the main thread, which is the thread that some tools (including the Eclipse IDE)
 *        expect to be the sole performer of file-system modifications.
 *
 * ---------------------------------------------------------------------------------------------------------------------
 *
 *    Summing up, the key facts about this phase are:
 *
 *      (i) Three pipelines run in parallel, thus allowing finishing earlier.
 *
 *     (ii) Pipelines 1 and 3 are sequential.
 *          In contrast, pipeline-2 uses task-parallelism (where each of the N workers is limited to invoking ASM and BType operations).
 *
 *          All three queues are concurrent:
 *
 *    (iii) Queue-1 connects a single producer (BCodePhase) to a single consumer (Worker-1),
 *          but given they run on different threads, queue-1 has to be concurrent.
 *
 *     (iv) Queue-2 is concurrent because concurrent workers of pipeline-2 take items from it.
 *
 *      (v) Queue-3 is concurrent (it's in fact a priority queue) because those same concurrent workers add items to it.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class GenBCode extends BCodeOptClosu {
  import global._

  val phaseName = "jvm"

  override def newPhase(prev: Phase) = new BCodePhase(prev)

  final class PlainClassBuilder(cunit: CompilationUnit) extends SyncAndTryBuilder(cunit)

  class BCodePhase(prev: Phase) extends StdPhase(prev) {

    override def name = phaseName
    override def description = "Generate bytecode from ASTs using the ASM library"
    override def erasedTypes = true

    val isOptimizRun  = settings.isIntraMethodOptimizOn

    // number of woker threads for pipeline-2 (the pipeline in charge of most optimizations except inlining).
    val MAX_THREADS = scala.math.min(
      if (isOptimizRun) 8 else 4,
      java.lang.Runtime.getRuntime.availableProcessors
    )

    private val woStarted = new java.util.concurrent.ConcurrentHashMap[Long, Long]  // debug
    private val woExited  = new java.util.concurrent.ConcurrentHashMap[Long, Item2] // debug

    private var bytecodeWriter  : BytecodeWriter   = null
    private var mirrorCodeGen   : JMirrorBuilder   = null
    private var beanInfoCodeGen : JBeanInfoBuilder = null

    /* ---------------- q1 ---------------- */

    case class Item1(arrivalPos: Int, cd: ClassDef, cunit: CompilationUnit) {
      def isPoison = { arrivalPos == Int.MaxValue }
    }
    private val poison1 = Item1(Int.MaxValue, null, null)
    private val q1 = new _root_.java.util.concurrent.LinkedBlockingQueue[Item1]

    /* ---------------- q2 ---------------- */

    case class Item2(arrivalPos:   Int,
                     mirror:       asm.tree.ClassNode,
                     plain:        asm.tree.ClassNode,
                     bean:         asm.tree.ClassNode,
                     lateClosures:      List[asm.tree.ClassNode],
                     dClosureEndpoints: Iterable[DClosureEndpoint],
                     outFolder:    _root_.scala.tools.nsc.io.AbstractFile) {
      def isPoison = { arrivalPos == Int.MaxValue }

      /* LCC-internal-name -> endpoint-as-MethodNode */
      def epByDCName: Map[String, MethodNode] = {

        if (dClosureEndpoints == null) {
          assert(lateClosures.isEmpty)
          return null
        }

        val isDelegateMethodName = (dClosureEndpoints map (epInfo => epInfo.epName)).toSet
        assert(isDelegateMethodName.size == dClosureEndpoints.size, "Names of endpoints should be unique within their master-class")

        val mnodeByName: Map[String, MethodNode] = (
          plain.toMethodList filter { mn => isDelegateMethodName(mn.name) } map { mn => Pair(mn.name, mn) }
        ).toMap

        val result =
          for(epInfo <- dClosureEndpoints)
          yield Pair(epInfo.closuBT.getInternalName, mnodeByName(epInfo.epName))

        result.toMap
      }
    }

    private val poison2 = Item2(Int.MaxValue, null, null, null, null, null, null)
    private val q2 = new _root_.java.util.concurrent.LinkedBlockingQueue[Item2]

    /* ---------------- q3 ---------------- */

    /*
     *  An item of queue-3 (the last queue before serializing to disk) contains three of these
     *  (one for each of mirror, plain, and bean classes).
     *
     *  @param jclassName  internal name of the class
     *  @param jclassBytes bytecode emitted for the class SubItem3 represents
     */
    case class SubItem3(
      jclassName:  String,
      jclassBytes: Array[Byte]
    )

    case class Item3(arrivalPos: Int,
                     mirror:     SubItem3,
                     plain:      SubItem3,
                     bean:       SubItem3,
                     outFolder:  _root_.scala.tools.nsc.io.AbstractFile) {

      def isPoison  = { arrivalPos == Int.MaxValue }

      /*
       * The first condition below (plain == null) implies WholeProgramAnalysis did the eliding,
       * the second condition holds when an intra-class optimization did the eliding
       * (during BCodeCleanser.cleanseClass(), running after whole-program).
       */
      def wasElided = {
        (plain == null) ||
        elidedClasses.contains(lookupRefBType(plain.jclassName))
      }

    }
    private val i3comparator = new _root_.java.util.Comparator[Item3] {
      override def compare(a: Item3, b: Item3) = {
        if (a.arrivalPos < b.arrivalPos) -1
        else if (a.arrivalPos == b.arrivalPos) 0
        else 1
      }
    }
    private val poison3 = Item3(Int.MaxValue, null, null, null, null)
    private val q3 = new _root_.java.util.concurrent.PriorityBlockingQueue[Item3](1000, i3comparator)

    /*
     *  Pipeline that takes ClassDefs from queue-1, lowers them into an intermediate form, placing them on queue-2
     *
     *  must-single-thread (because it relies on typer).
     */
    class Worker1(needsOutFolder: Boolean) extends _root_.java.lang.Runnable {

      val isDebugRun            = settings.debug.value
      val mustPopulateCodeRepo  = isIntraProgramOpt || isDebugRun

      val caseInsensitively = mutable.Map.empty[String, Symbol]
      var lateClosuresCount = 0

      def run() {
        while (true) {
          val item = q1.take
          if (item.isPoison) {
            isClassNodeBuildingDone = true
            for(i <- 1 to MAX_THREADS) { q2 put poison2 } // explanation in Worker2.run() as to why MAX_THREADS poison pills are needed on queue-2.
            return
          }
          else {
            try   { visit(item) }
            catch {
              case ex: Throwable =>
                ex.printStackTrace()
                error(s"Error while emitting ${item.cunit.source}\n${ex.getMessage}")
            }
          }
        }
      }

      /*
       *  Checks for duplicate internal names case-insensitively,
       *  builds ASM ClassNodes for mirror, plain, bean, and late-closure classes;
       *  enqueues them in queue-2, and
       *  incrementally populates dclosure-maps for the Late-Closure-Classes just built.
       *
       */
      def visit(item: Item1) {
        val Item1(arrivalPos, cd, cunit) = item
        val claszSymbol = cd.symbol

        // GenASM checks this before classfiles are emitted, https://github.com/scala/scala/commit/e4d1d930693ac75d8eb64c2c3c69f2fc22bec739
        val lowercaseJavaClassName = claszSymbol.javaClassName.toLowerCase
        caseInsensitively.get(lowercaseJavaClassName) match {
          case None =>
            caseInsensitively.put(lowercaseJavaClassName, claszSymbol)
          case Some(dupClassSym) =>
            item.cunit.warning(
              claszSymbol.pos,
              s"Class ${claszSymbol.javaClassName} differs only in case from ${dupClassSym.javaClassName}. " +
              "Such classes will overwrite one another on case-insensitive filesystems."
            )
        }

        // -------------- mirror class, if needed --------------
        val mirrorC =
          if (isStaticModule(claszSymbol) && isTopLevelModule(claszSymbol)) {
            if (claszSymbol.companionClass == NoSymbol) {
              mirrorCodeGen.genMirrorClass(claszSymbol, cunit)
            } else {
              log(s"No mirror class for module with linked class: ${claszSymbol.fullName}")
              null
            }
          } else null

        // -------------- "plain" class --------------
        val pcb = new PlainClassBuilder(cunit)
        pcb.genPlainClass(cd)
        val outF = if (needsOutFolder) getOutFolder(claszSymbol, pcb.thisName, cunit) else null;
        val plainC = pcb.cnode

        // -------------- bean info class, if needed --------------
        val beanC =
          if (claszSymbol hasAnnotation BeanInfoAttr) {
            beanInfoCodeGen.genBeanInfoClass(
              claszSymbol, cunit,
              fieldSymbols(claszSymbol),
              methodSymbols(cd)
            )
          } else null

        val lateClosures = pcb.lateClosures

        assert(lateClosures.isEmpty == pcb.closuresForDelegates.isEmpty)

        // ----------- all classes compiled in this run land in codeRepo.classes

        def trackInCodeRepo(compiled: asm.tree.ClassNode) {
          val bt = lookupRefBType(compiled.name)
          assert(!codeRepo.containsKey(bt))
          codeRepo.classes.put(bt, compiled)
        }

        if (mustPopulateCodeRepo) {
          trackInCodeRepo(plainC)
          lateClosures foreach trackInCodeRepo
          // mirror and bean classes need not be tracked in codeRepo.
        }

        // ----------- add entries for Late-Closure-Classes to exemplars ( "plain class" already tracked by virtue of initJClass() )

        for(lateC <- lateClosures) {
          // blanket invariant: after Worker1 each class (compiled or imported) has its `exemplars` counterpart. Ditto after Inlining.
          val trackedClosu = buildExemplarForLCC(lateC)
          exemplars.put(trackedClosu.c, trackedClosu)
        }

        // ----------- maps for dclosures (needed for optimizations, even inlining, and also for `squashOuterForLCC()`)

        var dClosureEndpoints: Iterable[DClosureEndpoint] = null
        if (lateClosures.nonEmpty) {
          val masterBT = lookupRefBType(plainC.name) // this is the "master class" responsible for "its" dclosures
          dClosureEndpoints = pcb.closuresForDelegates.values
          assert(lateClosures.size == dClosureEndpoints.size)
          populateDClosureMaps(plainC, masterBT, dClosureEndpoints)
        }

        val item2 =
          Item2(arrivalPos + lateClosuresCount,
                mirrorC, plainC, beanC,
                lateClosures, dClosureEndpoints,
                outF)

        // ----------- dead-code is removed before the inliner can see it.
        if (isIntraProgramOpt) {
          val essential = new EssentialCleanser(plainC)
          essential.codeFixupDCE()
          essential.codeFixupSquashLCC(lateClosures, item2.epByDCName)
        }

        // ----------- hand over to pipeline-2

        lateClosuresCount += lateClosures.size

        q2 put item2 // at the very end of this method so that no Worker2 thread starts mutating before we're done.

      } // end of method visit(Item1)

      /*
       *  precondition: the argument's internal name already registered as BType
       *
       *  Discussion on whether a Late-Closure-Class (LCC) needs to be an inner class. No it doesn't. Reasoning:
       *    (a) an LCC mentions only:
       *        (a.1) the types listed in its endpoint.
       *              The LCC's endpoint is a public method in a class C (the "master class" of the LCC).
       *        (a.2) type C, because the LCC's outer pointer points to C
       *    (b) Both C and LCC are in the same bytecode-level package.
       *
       *  Under -closurify:delegating or -closurify:MH , an anon-closure-class has no member classes.
       */
      private def buildExemplarForLCC(lateC: asm.tree.ClassNode): Tracked = {
        val key = lookupRefBType(lateC.name)
        val tsc: Tracked = exemplars.get(lookupRefBType(lateC.superName))
        val tr = Tracked(key, lateC.access, tsc, lateClosureInterfaces, EMPTY_InnerClassEntry_ARRAY)
        tr.directMemberClasses = Nil

        tr
      } // end of method buildExemplarForLCC

    } // end of class BCodePhase.Worker1

    /*
     *  Pipeline that takes ClassNodes from queue-2. The unit of work depends on the optimization level:
     *
     *    (a) no optimization involves:
     *          - removing dead code, and then
     *          - converting the plain ClassNode to byte array and placing it on queue-3
     *
     *    (b) with intra-procedural optimization on,
     *          - cleanseClass() is invoked on the plain class, and then
     *          - the plain class is serialized as above (ending up in queue-3)
     *
     *    (c) with inter-procedural optimization on,
     *          - cleanseClass() runs first.
     *            The difference with (b) however has to do with master-classes and their dclosures.
     *            In the inter-procedural case, they are processed as a single (larger) unit of work by cleanseClass.
     *            That's why in this case "large classes" (see `i2LargeClassesFirst`) bubble up to queue-2's head.
     *          - once that (larger) unit of work is complete, all of its constituent classes are placed on queue-3.
     *
     *  can-multi-thread
     */
    class Worker2 extends _root_.java.lang.Runnable {

      def run() {

        val id = java.lang.Thread.currentThread.getId
        woStarted.put(id, id)

        while (true) {
          val item = q2.take
          if (item.isPoison) {
            woExited.put(id, item)
            q3 put poison3 // therefore queue-3 will contain as many poison pills as pipeline-2 threads.
            // to terminate all pipeline-2 workers, queue-1 must contain as many poison pills as pipeline-2 threads.
            return
          }
          else {
            try   { visit(item) }
            catch {
              case ex: Throwable =>
                ex.printStackTrace()
                error(s"Error while emitting ${item.plain.name}\n${ex.getMessage}")
            }
          }
        }
      }

      /*
       *  Performs optimizations using task parallelism.
       *  A task has exclusive access to ASM ClassNodes that need to be mutated in-tandem,
       *  for example a master class and the dclosures it's responsible for.
       *  Afterwards, adds the ClassNode(s) to queue-3.
       */
      def visit(item: Item2) {

        assert(isInliningDone == isIntraProgramOpt)

        val cnode   = item.plain
        val cnodeBT = lookupRefBType(cnode.name)

        if (isOptimizRun) {
          val cleanser = new BCodeCleanser(cnode, isIntraProgramOpt)
          cleanser.codeFixupDCE()
          cleanser.codeFixupSquashLCC(item.lateClosures, item.epByDCName)
          cleanser.cleanseClass()
        }
        else {
          // the minimal fixups needed, even for unoptimized runs.
          val essential = new EssentialCleanser(cnode)
          essential.codeFixupDCE()
          essential.codeFixupSquashLCC(item.lateClosures, item.epByDCName)
        }

        refreshInnerClasses(cnode)
        item.lateClosures foreach refreshInnerClasses

        addToQ3(item)

      } // end of method visit(Item2)

      private def addToQ3(item: Item2) {

        def getByteArray(cn: asm.tree.ClassNode): Array[Byte] = {
          val cw = new CClassWriter(extraProc)
          cn.accept(cw)
          cw.toByteArray
        }

        val Item2(arrivalPos, mirror, plain, bean, lateClosures, _, outFolder) = item

        val mirrorC = if (mirror == null) null else SubItem3(mirror.name, getByteArray(mirror))
        val plainC  = SubItem3(plain.name, getByteArray(plain))
        val beanC   = if (bean == null)   null else SubItem3(bean.name, getByteArray(bean))

        q3 put Item3(arrivalPos, mirrorC, plainC, beanC, outFolder)

        // -------------- Late-Closure-Classes, if any --------------
        var lateClosuresCount = 0
        for(lateC <- lateClosures.reverse) {
          lateClosuresCount += 1
          q3 put Item3(arrivalPos + lateClosuresCount, null, SubItem3(lateC.name, getByteArray(lateC)), null, outFolder)
        }

      }

    } // end of class BCodePhase.Worker2

    var arrivalPos = 0

    /*
     *  A run of the BCodePhase phase comprises:
     *
     *    (a) set-up steps (most notably supporting maps in `BCodeTypes`,
     *        but also "the" writer where class files in byte-array form go)
     *
     *    (b) building of ASM ClassNodes, their optimization and serialization.
     *
     *    (c) tear down (closing the classfile-writer and clearing maps)
     *
     */
    override def run() {

      log(s"Early anon-closures: ${uncurry.convertedTraditional} Late anon-closures: ${uncurry.convertedModern}")

      arrivalPos = 0 // just in case
      scalaPrimitives.init
      initBCodeOpt()

      // initBytecodeWriter invokes fullName, thus we have to run it before the typer-dependent thread is activated.
      bytecodeWriter  = initBytecodeWriter(cleanup.getEntryPoints)
      mirrorCodeGen   = new JMirrorBuilder
      beanInfoCodeGen = new JBeanInfoBuilder

      val needsOutfileForSymbol = bytecodeWriter.isInstanceOf[ClassBytecodeWriter]
      if (isIntraProgramOpt) {
        wholeProgramThenWriteToDisk(needsOutfileForSymbol)
      } else {
        buildAndSendToDiskInParallel(needsOutfileForSymbol)
      }

      // closing output files.
      bytecodeWriter.close()

      /* TODO Bytecode can be verified (now that all classfiles have been written to disk)
       *
       * (1) asm.util.CheckAdapter.verify()
       *       public static void verify(ClassReader cr, ClassLoader loader, boolean dump, PrintWriter pw)
       *     passing a custom ClassLoader to verify inter-dependent classes.
       *     Alternatively,
       *       - an offline-bytecode verifier could be used (e.g. Maxine brings one as separate tool).
       *       - -Xverify:all
       *
       * (2) if requested, check-java-signatures, over and beyond the syntactic checks in `getGenericSignature()`
       *
       */

      // clearing maps
      clearBCodeOpt()
    }

    /*
     *  The workflow where inter-procedural optimizations is ENABLED comprises:
     *    (a) sequentially build all ClassNodes (Worker1 takes care of this)
     *    (b) sequentially perform whole-program analysis on them
     *    (c) run in parallel:
     *          - intra-class (including intra-method) optimizations
     *          - a limited form of inter-class optimizations
     *            (those affecting a master-class and the delegating-closures it's responsible for, details below)
     *    (d) overlapping with (c), write non-elided classes to disk.
     *
     *  A useful distinction of inter-class optimizations involves:
     *    (e) method-inlining and closure-inlining, ie what `BCodeOptInter.WholeProgramAnalysis`  does
     *    (f) the "limited form" referred to above, ie what `BCodeOptInter.DClosureOptimizerImpl` does
     *        Unlike (e), different groups of ClassNodes in (f) can be optimized in parallel,
     *        where a "group" comprises a master-class and the dclosures the master-class is responsible for.
     *
     *  The distinction is useful because it explains why Item2 has a fields for Late-Closure-Classes:
     *  that way, LCCs are added to queue-3 only after all optimizations
     *  triggered by the master class have been completed, including (f).
     *  Otherwise the ClassNode for a delegating-closure could be written to disk too early.
     *
     */
    private def wholeProgramThenWriteToDisk(needsOutFolder: Boolean) {
      assert(isIntraProgramOpt)

      // sequentially
      feedPipeline1()
      (new Worker1(needsOutFolder)).run()
      (new WholeProgramAnalysis).optimize()

      // optimize different groups of ClassNodes in parallel, once done with each group queue its ClassNodes for disk serialization.
      spawnPipeline2()
      // overlapping with pipeline-2, serialize to disk.
      drainQ3()

    }

    /*
     *  The workflow where inter-procedural optimizations is DISABLED boils down to:
     *  As soon as each individual ClassNode is ready
     *     (if needed intra-class optimized,
     *     moreover optimized with the Late-Closure-Classes it's responsible for)
     *  it's also ready for disk serialization, ie it's ready to be added to queue-3.
     *
     */
    private def buildAndSendToDiskInParallel(needsOutFolder: Boolean) {
      assert(!isIntraProgramOpt)

      new _root_.java.lang.Thread(new Worker1(needsOutFolder), "bcode-typer").start()
      spawnPipeline2()
      feedPipeline1()
      drainQ3()

    }

    /* Feed pipeline-1: place all ClassDefs on q1, recording their arrival position. */
    private def feedPipeline1() {
      super.run()
      q1 put poison1
    }

    /* Pipeline from q2 to q3. */
    private def spawnPipeline2(): IndexedSeq[Thread] = {
      for(i <- 1 to MAX_THREADS) yield {
        val w = new Worker2
        val t = new _root_.java.lang.Thread(w, "optimizer-" + i)
        t.start()
        t
      }
    }

    /* Pipeline that writes classfile representations to disk. */
    private def drainQ3() {

      def sendToDisk(cfr: SubItem3, outFolder: _root_.scala.tools.nsc.io.AbstractFile) {
        if (cfr != null){
          val SubItem3(jclassName, jclassBytes) = cfr
          try {
            val outFile =
              if (outFolder == null) null
              else getFileForClassfile(outFolder, jclassName, ".class")
            bytecodeWriter.writeClass(jclassName, jclassName, jclassBytes, outFile)
          }
          catch {
            case e: FileConflictException =>
              error(s"error writing $jclassName: ${e.getMessage}")
          }
        }
      }

      var moreComing = true
      var remainingWorkers = MAX_THREADS
      // `expected` denotes the arrivalPos whose Item3 should be serialized next
      var expected = 0
      // `followers` contains items that arrived too soon, they're parked waiting for `expected` to be polled from queue-3
      val followers = new java.util.PriorityQueue[Item3](100, i3comparator)

      while (moreComing) {
        val incoming = q3.take
        if (incoming.isPoison) {
          remainingWorkers -= 1
          moreComing = (remainingWorkers != 0)
        } else {
          followers.add(incoming)
        }
        if (!moreComing) {
          val queuesOK = (q3.isEmpty && followers.isEmpty)
          if (!queuesOK) {
            error("GenBCode found class files waiting in queues to be written but an error prevented doing so.")
          }
        }
        while (!followers.isEmpty && followers.peek.arrivalPos == expected) {
          val item = followers.poll
          if (!item.wasElided) {
            val outFolder = item.outFolder
            sendToDisk(item.mirror, outFolder)
            sendToDisk(item.plain,  outFolder)
            sendToDisk(item.bean,   outFolder)
          }
          expected += 1
        }
      }

      // we're done
      assert(q1.isEmpty, s"Some ClassDefs remained in the first queue: $q1")
      assert(q2.isEmpty, s"Some classfiles remained in the second queue: $q2")
      assert(q3.isEmpty, s"Some classfiles weren't written to disk: $q3")

    }

    /*
     *  Apply BCode phase to a compilation unit: enqueue each contained ClassDef in queue-1,
     *  so as to release the main thread for a duty it cannot delegate: writing classfiles to disk.
     *  See `drainQ3()`
     */
    override def apply(cunit: CompilationUnit): Unit = {

      def gen(tree: Tree) {
        tree match {
          case EmptyTree            => ()
          case PackageDef(_, stats) => stats foreach gen
          case cd: ClassDef         =>
            q1 put Item1(arrivalPos, cd, cunit)
            arrivalPos += 1
        }
      }

      gen(cunit.body)
    }

    /*
     *  Adds entries to `closuRepo.dclosures` and `closuRepo.endpoint` for the Late-Closure-Classes just built.
     *
     *  After `BCodePhase.Worker1.visit()` has run
     *    (to recap, Worker1 takes ClassDefs as input and lowers them to ASM ClassNodes)
     *  for a plain class C, we know that all instantiations of C's Late-Closure-Classes are enclosed in C.
     *    (the only exceptions to this resulted in the past from a rewriting not performed that way anymore,
     *     by which DelayedInit delayed-initialization-statements would be transplanted to a separate closure-class;
     *     nowadays the rewriting is such that those statements remain in the class originally enclosing them,
     *     but in a different method).
     *     @see [[scala.tools.nsc.transform.Constructors]]'s `delayedEndpointDef()`
     *
     *  Looking ahead, `BCodeOptInter.WholeProgramAnalysis.inlining()`
     *  may break the property above (ie inlining may result in lambda usages,
     *  be they instantiations or endpoint-invocations, being transplanted to a class different from that
     *  originally enclosing them). Tracking those cases is the job of
     *  `BCodeOptInter.closuRepo.trackClosureUsageIfAny()`
     *
     *  Coming back to the property holding
     *  right after `BCodePhase.Worker1.visit()` has run for a plain class C
     *    (the property that all instantiations of C's Late-Closure-Classes are enclosed in C)
     *  details about that property are provided by map `dclosures` (populated by `genLateClosure()`).
     *  That map lets us know, given a plain class C, the Late-Closure-Classes it's responsible for.
     *
     *  @param cnode    the "master class" responsible for "its" dclosures
     *  @param masterBT BType of cnode
     *  @param dClosureEndpoints see `PlainClassBuilder.closuresForDelegates`
     *
     */
    def populateDClosureMaps(cnode: asm.tree.ClassNode, masterBT: BType, dClosureEndpoints: Iterable[DClosureEndpoint]) {

      // add entry to `closuRepo.endpoint`
      val isDelegateMethodName = (dClosureEndpoints map (dce => dce.epName)).toSet
      val candidateMethods = (cnode.toMethodList filter (mn => isDelegateMethodName(mn.name)))
      for(dClosureEndpoint <- dClosureEndpoints) {
        val candidates: List[MethodNode] =
          for(
            mn <- candidateMethods;
            if (mn.name == dClosureEndpoint.epName) && (mn.desc == dClosureEndpoint.epMT.getDescriptor)
          ) yield mn;

        assert(candidates.nonEmpty && candidates.tail.isEmpty)
        val delegateMethodNode = candidates.head

        // so that it can be invoked from another class (its Late-Closure-Class)
        asm.optimiz.Util.makePublicMethod(delegateMethodNode)

        val delegateMethodRef = MethodRef(masterBT, delegateMethodNode)
        closuRepo.endpoint.put(dClosureEndpoint.closuBT, delegateMethodRef)
      }

      // add entry to `closuRepo.dclosures`
      for(dClosureEndpoint <- dClosureEndpoints) {
        val others0 = closuRepo.dclosures.get(masterBT)
        val others  = if (others0 == null) Nil else others0
        closuRepo.dclosures.put(masterBT, dClosureEndpoint.closuBT :: others)
      }

    } // end of method populateDClosureMaps()

  } // end of class BCodePhase

} // end of class GenBCode
