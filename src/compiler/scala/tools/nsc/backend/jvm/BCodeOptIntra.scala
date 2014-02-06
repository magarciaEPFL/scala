/* NSC -- new Scala compiler
 * Copyright 2005-2013 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import backend.bcode.{ProdConsAnalyzer, Util}
import asm.tree.analysis.SourceValue
import asm.tree._

import scala.collection.{ mutable, immutable }

/*
 *  Optimize and tidy-up bytecode before it's serialized for good.
 *  This class focuses on
 *    - intra-method optimizations,
 *    - intra-class  optimizations, and
 *    - utilities for the above and for inter-procedural optimizations as well.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 *  TODO Improving the Precision and Correctness of Exception Analysis in Soot, http://www.sable.mcgill.ca/publications/techreports/#report2003-3
 *
 */
abstract class BCodeOptIntra extends BCodeOuterSquash {

  import global._

  /*
   *  All methods in this class can-multi-thread, provided each thread uses a dedicated instance of EssentialCleaner.
   *
   *  In more detail:
   *    - each worker thread has its own dedicated instance of EssentialCleanser,
   *      and in turn each such instance owns a (thus per-thread) JumpChainsCollapser, etc.
   *    - an invocation of EssentialCleanser.cleanseMethod() runs without spawning itself any threads,
   *      in a sequential manner; that's why there's no concurrent access to the same JumpChainsCollapser, etc.
   *      (otherwise, that would amount to a race-condition).
   *
   */
  class EssentialCleanser(cnode: asm.tree.ClassNode) {

    val jumpsCollapser      = new backend.bcode.JumpChainsCollapser()
    val unreachCodeRemover  = new backend.bcode.UnreachableCode()
    val labelsCleanup       = new backend.bcode.LabelsCleanup()
    val danglingExcHandlers = new backend.bcode.DanglingExcHandlers()

    /*
     *  This method performs a few intra-method optimizations:
     *    - collapse a multi-jump chain to target its final destination via a single jump
     *    - remove unreachable code
     *    - remove those LabelNodes and LineNumbers that aren't in use
     *
     *  Some of the above are applied repeatedly until no further reductions occur.
     *
     *  Node: what ICode calls reaching-defs is available as asm.tree.analysis.SourceInterpreter, but isn't used here.
     *
     */
    final def cleanseMethod(cName: String, mnode: asm.tree.MethodNode): Boolean = {

      var changed = false
      var keepGoing = false

      do {
        keepGoing = false

        jumpsCollapser.transform(mnode)            // collapse a multi-jump chain to target its final destination via a single jump
        keepGoing |= jumpsCollapser.changed

        unreachCodeRemover.transform(cName, mnode) // remove unreachable code
        keepGoing |= unreachCodeRemover.changed

        labelsCleanup.transform(mnode)             // remove those LabelNodes and LineNumbers that aren't in use
        keepGoing |= labelsCleanup.changed

        danglingExcHandlers.transform(mnode)
        keepGoing |= danglingExcHandlers.changed

        changed |= keepGoing

      } while (keepGoing)

      changed

    }

    /*
     *  Removes dead code.
     *
     *  When writing classfiles with "optimization level zero" (ie -Ybackend:GenBCode)
     *  the very least we want to do is remove dead code beforehand,
     *  so as to prevent an artifact of stack-frames computation from showing up,
     *  the artifact described at http://asm.ow2.org/doc/developer-guide.html#deadcode
     *  That artifact results from the requirement by the Java 6 split verifier
     *  that a stack map frame be available for each basic block, even unreachable ones.
     *
     *  Just removing dead code might leave stale LocalVariableTable entries
     *  thus `cleanseMethod()` also gets rid of those.
     *
     */
    final def codeFixupDCE() {
      ifDebug { runTypeFlowAnalysis() }
      val iter = cnode.methods.iterator()
      while (iter.hasNext) {
        val mnode = iter.next()
        if (Util.hasBytecodeInstructions(mnode)) {
          Util.computeMaxLocalsMaxStack(mnode)
          cleanseMethod(cnode.name, mnode) // remove unreachable code
        }
      }
      ifDebug { runTypeFlowAnalysis() }
    }

    /*
     *  Elide redundant outer-fields for Late-Closure-Classes.
     *
     *  @param lccsToSquashOuterPointer in this case, what the name implies.
     *  @param dClosureEndpoint         a map with entries (LCC-internal-name -> endpoint-as-MethodNode)
     *
     */
    final def codeFixupSquashLCC(lccsToSquashOuterPointer: List[ClassNode],
                                 dClosureEndpoint: Map[String, MethodNode]) {
      if (!cnode.isStaticModule && lccsToSquashOuterPointer.nonEmpty) {
        val sq = new LCCOuterSquasher(cnode, lccsToSquashOuterPointer, dClosureEndpoint)
        sq.squashOuterForLCC()
      }
      ifDebug { runTypeFlowAnalysis() }
    }

    //--------------------------------------------------------------------
    // Type-flow analysis
    //--------------------------------------------------------------------

    final def runTypeFlowAnalysis() {
      for(m <- cnode.toMethodList; if Util.hasBytecodeInstructions(m)) {
        runTypeFlowAnalysis(m)
      }
    }

    final def runTypeFlowAnalysis(mnode: MethodNode) {

      import asm.tree.analysis.{ Analyzer, Frame }
      import asm.tree.AbstractInsnNode

      Util.computeMaxLocalsMaxStack(mnode)
      val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
      tfa.analyze(cnode.name, mnode)
      val frames: Array[Frame[TFValue]]   = tfa.getFrames()
      val insns:  Array[AbstractInsnNode] = mnode.instructions.toArray()
      var i = 0
      while (i < insns.length) {
        if (frames(i) == null && insns(i) != null) {
          // TODO abort("There should be no unreachable code left by now.")
        }
        i += 1
      }
    }

  } // end of class EssentialCleanser

  class QuickCleanser(cnode: asm.tree.ClassNode) extends EssentialCleanser(cnode) {

    val copyPropagator      = new backend.bcode.CopyPropagator
    val deadStoreElimPrim   = new backend.bcode.DeadStoreElimPrim
    val deadStoreElimRef    = new backend.bcode.DeadStoreElimRef
    val ppCollapser         = new backend.bcode.PushPopCollapser
    val jumpReducer         = new backend.bcode.JumpReducer
    val nullnessPropagator  = new backend.bcode.NullnessPropagator
    val constantFolder      = new backend.bcode.ConstantFolder

    //--------------------------------------------------------------------
    // First optimization pack
    //--------------------------------------------------------------------

    /*
     *  Intra-method optimizations performed until a fixpoint is reached.
     */
    final def basicIntraMethodOpt(mnode: asm.tree.MethodNode) {
      val cName = cnode.name
      var keepGoing = false
      do {
        keepGoing = false

        keepGoing |= cleanseMethod(cName, mnode)
        keepGoing |= elimRedundantCode(cName, mnode)

        nullnessPropagator.transform(cName, mnode);   // infers null resp. non-null reaching certain program points, simplifying control-flow based on that.
        keepGoing |= nullnessPropagator.changed

        constantFolder.transform(cName, mnode);       // propagates primitive constants, performs ops and simplifies control-flow based on that.
        keepGoing |= constantFolder.changed

      } while (keepGoing)
    }

    //--------------------------------------------------------------------
    // Second optimization pack
    //--------------------------------------------------------------------

    /*
     *  This method performs a few intra-method optimizations,
     *  aimed at reverting the extra copying introduced by inlining:
     *    - replace the last link in a chain of data accesses by a direct access to the chain-start.
     *    - dead-store elimination
     *    - remove those (producer, consumer) pairs where the consumer is a DROP and
     *      the producer has its value consumed only by the DROP in question.
     *
     */
    final def elimRedundantCode(cName: String, mnode: asm.tree.MethodNode): Boolean = {
      var changed   = false
      var keepGoing = false

      do {

        keepGoing = false

        copyPropagator.transform(cName, mnode) // replace the last link in a chain of data accesses by a direct access to the chain-start.
        keepGoing |= copyPropagator.changed

        deadStoreElimPrim.transform(cName, mnode)  // replace STOREs to non-live local-vars with DROP instructions.
        keepGoing |= deadStoreElimPrim.changed

        deadStoreElimRef.transform(cName, mnode)   // replace STOREs to non-live local-vars with DROP instructions.
        keepGoing |= deadStoreElimRef.changed

        ppCollapser.transform(cName, mnode)    // propagate a DROP to the instruction(s) that produce the value in question, drop the DROP.
        keepGoing |= ppCollapser.changed

        jumpReducer.transform(mnode)           // simplifies branches that need not be taken to get to their destination.
        keepGoing |= jumpReducer.changed

        changed = (changed || keepGoing)

      } while (keepGoing)

      changed
    }

  } // end of class QuickCleanser

  /*
   *  Intra-method optimizations. Upon visiting each method in an asm.tree.ClassNode,
   *  optimizations are applied iteratively until a fixpoint is reached.
   *
   *  All optimizations implemented here can do based solely on information local to the method
   *  (in particular, no lookups on `exemplars` are performed).
   *  That way, intra-method optimizations can be performed in parallel (in pipeline-2)
   *  while GenBCode's pipeline-1 keeps building more `asm.tree.ClassNode`s.
   *  Moreover, pipeline-2 is realized by a thread-pool.
   *
   *  The entry point is `cleanseClass()`.
   */
  final class BCodeCleanser(cnode: asm.tree.ClassNode) extends QuickCleanser(cnode) {

    val unboxElider           = new backend.bcode.UnBoxElider
    val lvCompacter           = new backend.bcode.LocalVarCompact

    /*
     *  The intra-method optimizations below are performed until a fixpoint is reached.
     *  They are grouped somewhat arbitrarily into:
     *    - those performed by `cleanseMethod()`
     *    - those performed by `elimRedundandtCode()`
     *    - nullness propagation
     *    - constant folding
     *
     *  After the fixpoint has been reached, three more intra-method optimizations are performed just once
     *  (further applications wouldn't reduce any further):
     *    - eliding box/unbox pairs
     *    - eliding redundant local vars
     *
     *  An introduction to ASM bytecode rewriting can be found in Ch. 8. "Method Analysis" in
     *  the ASM User Guide, http://download.forge.objectweb.org/asm/asm4-guide.pdf
     *
     *  TODO refreshInnerClasses() should also be run on dclosures
     */
    def cleanseClass() {

      // a dclosure is optimized together with its master class by `DClosureOptimizer`
      assert(!isDClosure(cnode.name), s"A delegating-closure pretented to be optimized as plain class: ${cnode.name}")

      val bt = lookupRefBType(cnode.name)
      if (wasElided(bt)) { return }

      // (1) intra-method
      intraMethodFixpoints(full = true)

    } // end of method cleanseClass()

    /*
     *  intra-method optimizations
     */
    def intraMethodFixpoints(full: Boolean) {

      for(mnode <- cnode.toMethodList; if Util.hasBytecodeInstructions(mnode)) {

        Util.computeMaxLocalsMaxStack(mnode)

        basicIntraMethodOpt(mnode)                 // intra-method optimizations performed until a fixpoint is reached

        if (full) {
          unboxElider.transform(cnode.name, mnode) // remove box/unbox pairs (this transformer is more expensive than most)
          lvCompacter.transform(mnode)             // compact local vars, remove dangling LocalVariableNodes.
        }

        ifDebug { runTypeFlowAnalysis(mnode) }

      }

    }

  } // end of class BCodeCleanser

  /*
   * One of the intra-method optimizations (dead-code elimination)
   * and a few of the inter-procedural ones (inlining)
   * may have caused the InnerClasses JVM attribute to become stale
   * (e.g. some inner classes that were mentioned aren't anymore,
   * or inlining added instructions referring to inner classes not yet accounted for)
   *
   * This method takes care of SI-6546 "Optimizer leaves references to classes that have been eliminated by inlining"
   *
   * TODO SI-6759 Seek clarification about necessary and sufficient conditions to be listed in InnerClasses JVM attribute (GenASM).
   * The JVM spec states in Sec. 4.7.6 that
   *   for each CONSTANT_Class_info (constant-pool entry) which represents a class or interface that is not a member of a package
   * an entry should be made in the class' InnerClasses JVM attribute.
   * According to the above, the mere fact an inner class is mentioned in, for example, an annotation
   * wouldn't be reason enough for adding it to the InnerClasses JVM attribute.
   * However that's what GenASM does. Instead, this method scans only those internal names that will make it to a CONSTANT_Class_info.
   *
   * `refreshInnerClasses()` requires that `exemplars` already tracks
   * each BType of hasObjectSort variety that is mentioned in the ClassNode.
   *
   * can-multi-thread
   */
  final def refreshInnerClasses(cnode: ClassNode) {

    import collection.JavaConverters._

    val refedInnerClasses = mutable.Set.empty[BType]
    cnode.innerClasses.clear()

    def visitInternalName(value: String) {
      if (value == null) {
        return
      }
      var bt = lookupRefBType(value)
      if (bt.isArray) {
        bt = bt.getElementType
      }
      if (bt.hasObjectSort && !bt.isPhantomType && (bt != BoxesRunTime) && !wasElided(bt)) {
        if (exemplars.get(bt).isInnerClass) {
          refedInnerClasses += bt
        }
      }
    }

    def visitDescr(desc: String) {
      if(desc.startsWith("(")) {
        val mt = BMType(desc)
        visitDescr(mt.returnType.getDescriptor)
        mt.argumentTypes foreach { at => visitDescr(at.getDescriptor) }
      } else {
        val bt = descrToBType(desc)
        if (bt.isArray) {
          visitDescr(bt.getElementType.getDescriptor)
        }
        else if (bt.hasObjectSort) {
          visitInternalName(bt.getInternalName)
        }
      }
    }

    visitInternalName(cnode.name)
    visitInternalName(cnode.superName)
    cnode.interfaces.asScala foreach visitInternalName
    visitInternalName(cnode.outerClass)
    cnode.fields.asScala  foreach { fn: FieldNode  => visitDescr(fn.desc) }
    cnode.methods.asScala foreach { mn: MethodNode => visitDescr(mn.desc) }

    // annotations not visited because they store class names in CONSTANT_Utf8_info as opposed to the CONSTANT_Class_info that matter for InnerClasses.

    // TODO JDK8 the BootstrapMethodsAttribute may point via bootstrap_arguments to one or more CONSTANT_Class_info entries

    for(m <- cnode.methods.asScala) {

      m.exceptions.asScala foreach visitInternalName

      m.tryCatchBlocks.asScala foreach { tcb => visitInternalName(tcb.`type`) }

      val iter = m.instructions.iterator()
      while (iter.hasNext) {
        val insn = iter.next()
        insn match {
          case ti: TypeInsnNode   => visitInternalName(ti.desc) // an intenal name, actually
          case fi: FieldInsnNode  => visitInternalName(fi.owner); visitDescr(fi.desc)
          case mi: MethodInsnNode => visitInternalName(mi.owner); visitDescr(mi.desc)
          case ivd: InvokeDynamicInsnNode => () // TODO
          case ci: LdcInsnNode    =>
            ci.cst match {
              case t: asm.Type => visitDescr(t.getDescriptor)
              case _           => ()
            }
          case ma: MultiANewArrayInsnNode => visitDescr(ma.desc)
          case _ => ()
        }
      }

    }

    // cnode is a class being compiled, thus its Tracked.directMemberClasses should be defined
    // TODO check whether any member class has been elided? (but only anon-closure-classes can be elided)
    refedInnerClasses ++= exemplars.get(lookupRefBType(cnode.name)).directMemberClasses

    addInnerClassesASM(cnode, refedInnerClasses)

  } // end of method refreshInnerClasses()

} // end of class BCodeOptIntra
