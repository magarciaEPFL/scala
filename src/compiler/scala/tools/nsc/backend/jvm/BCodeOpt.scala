/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.{UnBoxAnalyzer, Util}
import asm.tree.analysis.SourceValue
import asm.tree._

import scala.collection.{ mutable, immutable }
import scala.Some
import collection.convert.Wrappers.JListWrapper

/**
 *  Optimize and tidy-up bytecode before it's emitted for good.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 *  TODO Improving the Precision and Correctness of Exception Analysis in Soot, http://www.sable.mcgill.ca/publications/techreports/#report2003-3
 *
 */
abstract class BCodeOpt extends BCodeTypes {

  import global._

  /**
   * Set of known JVM-level getters and fields allowing access to stable values
   * A stable path must consist only of stable links, ie the receiver of a stable getter itself must be stable,
   * and simimlarly for fields.
   */
  val repeatableReads = new StableMembersSet

  val knownLacksInline = mutable.Set.empty[Symbol] // cache to avoid multiple inliner.hasInline() calls.
  val knownHasInline   = mutable.Set.empty[Symbol] // as above. Motivated by the need to warn on "inliner failures".

  def hasInline(sym: Symbol) = {
    if     (knownLacksInline(sym)) false
    else if(knownHasInline(sym))   true
    else {
      val b = (sym hasAnnotation definitions.ScalaInlineClass)
      if(b) { knownHasInline   += sym }
      else  { knownLacksInline += sym }

      b
    }
  }

  def hasNoInline(sym: Symbol) = sym hasAnnotation definitions.ScalaNoInlineClass

  val cgns = new mutable.PriorityQueue[CallGraphNode]()(cgnOrdering)

  /**
   *  @param owner      a JVM-level class
   *  @param memberName name of a method or field defined in `owner`
   *  @param memberType the member's type ie a MethodType denotes "name" refers to a method, otherwise to a field.
   *
   */
  case class StableMember(owner: BType, memberName: String, memberType: BType) { // TODO lookupTermName rather than String for memberName

    /** Can't be made into an assert because building a StableMember for use as lookup key is valid, even though that StableMember may be non-well-formed. */
    def isRepOK: Boolean = {
      if(memberType.sort == asm.Type.METHOD) { memberType.getArgumentCount == 0 && !memberType.getReturnType.isUnitType } else { true }
    }

    def getSize: Int = {
      if (memberType.sort == asm.Type.METHOD) memberType.getReturnType.getSize
      else memberType.getSize
    }

  }

  class StableMembersSet extends mutable.HashSet[StableMember] {

    def markAsRepeatableRead(owner: BType, memberName: String, memberType: BType) {
      this += StableMember(owner, memberName, memberType)
    }

    def isKnownRepeatableRead(owner: BType, memberName: String, memberType: BType): Boolean = {
      contains(StableMember(owner, memberName, memberType))
    }

  }

  /**
   * must-single-thread
   **/
  def clearBCodeOpt() {
    repeatableReads.clear()
    knownLacksInline.clear()
    knownHasInline.clear()
    cgns.clear()
    codeRepo.clear()
  }

  /**
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
  class BCodeCleanser(cnode: asm.tree.ClassNode) {

    val jumpsCollapser      = new asm.optimiz.JumpChainsCollapser(null)
    val unreachCodeRemover  = new asm.optimiz.UnreachableCode
    val labelsCleanup       = new asm.optimiz.LabelsCleanup(null)
    val danglingExcHandlers = new asm.optimiz.DanglingExcHandlers(null)

    val copyPropagator      = new asm.optimiz.CopyPropagator
    val deadStoreElim       = new asm.optimiz.DeadStoreElim
    val ppCollapser         = new asm.optimiz.PushPopCollapser
    val unboxElider         = new asm.optimiz.UnBoxElider
    val jumpReducer         = new asm.optimiz.JumpReducer(null)
    val nullnessPropagator  = new asm.optimiz.NullnessPropagator
    val constantFolder      = new asm.optimiz.ConstantFolder

    val lvCompacter         = new asm.optimiz.LocalVarCompact(null)

    cleanseClass();

    /**
     *  The (intra-method) optimizations below are performed until a fixpoint is reached.
     *  They are grouped somewhat arbitrarily into:
     *    - those performed by `cleanseMethod()`
     *    - those performed by `elimRedundandtCode()`
     *    - nullness propagation
     *    - constant folding
     *
     *  After the fixpoint has been reached, two more optimizations are performed just once
     *  (further applications wouldn't reduce any further):
     *    - eliding box/unbox pairs
     *    - eliding redundant local vars.
     *
     *  An introduction to ASM bytecode rewriting can be found in Ch. 8. "Method Analysis" in
     *  the ASM User Guide, http://download.forge.objectweb.org/asm/asm4-guide.pdf
     */
    def cleanseClass() {
      // find out maxLocals and maxStack (maxLocals is given by nxtIdx in PlainClassBuilder, but maxStack hasn't been computed yet).
      val cw = new asm.ClassWriter(asm.ClassWriter.COMPUTE_MAXS)
      cnode.accept(cw)

      val mwIter = cw.getMethodWriters().iterator
      val mnIter = cnode.methods.iterator()

      while(mnIter.hasNext) {
        val mnode = mnIter.next()
        val mw    = mwIter.next()
        mnode.visitMaxs(mw.getMaxStack, mw.getMaxLocals)
        val isConcrete = ((mnode.access & (asm.Opcodes.ACC_ABSTRACT | asm.Opcodes.ACC_NATIVE)) == 0)
        if(isConcrete) {
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

          } while(keepGoing)

          cacheRepeatableReads(cName, mnode)

          unboxElider.transform(cName, mnode)   // remove box/unbox pairs (this transformer is more expensive than most)
          lvCompacter.transform(mnode)          // compact local vars, remove dangling LocalVariableNodes.

          // val before = text(cnode.innerClasses)
          refreshInnerClasses(cnode)
          // val after  = text(cnode.innerClasses)

          runTypeFlowAnalysis(cName, mnode) // debug
        }
      }
    }

    /* TODO for debug only */
    def text(ics: java.util.List[InnerClassNode]): String = {
      if(ics == null) { return null }
      val res = new StringBuilder()
      val iter = ics.iterator()
      while(iter.hasNext) {
        val n: InnerClassNode = iter.next()
        val line = "(name: " + n.name + " outerName " + n.outerName + " innerName " + n.innerName + " " + n.access + ")"
        res.append(line + "\n")
      }
      res.toString
    }

    /**
     * One of the intra-method optimizations (dead-code elimination)
     * and a few of the inter-procedural ones (inlining)
     * may have caused the InnerClass JVM attribute to become stale
     * (e.g. some inner classes that were mentioned aren't anymore,
     * or inlining added instructions referring to inner classes not yet accounted for)
     *
     * This method takes care of SI-6546 Optimizer leaves references to classes that have been eliminated by inlining
     *
     * TODO SI-6759 Seek clarification about necessary and sufficient conditions to be listed in InnerClasses JVM attribute (GenASM).
     * The JVM spec states in Sec. 4.7.6 that
     *   for each CONSTANT_Class_info (constant-pool entry) which represents a class or interface that is not a member of a package
     * an entry should be made in the class' InnerClasses JVM attribute.
     * According to the above, the mere fact an inner class is mentioned in, for example, an annotation
     * wouldn't be reason enough for adding it to the InnerClasses JVM attribute.
     * However that's what GenASM does. Instead, this method scans only those internal names that will make it to a CONSTANT_Class_info.
     */
    private def refreshInnerClasses(cnode: ClassNode) {

      import scala.collection.convert.Wrappers.JListWrapper

      var refedInnerClasses = mutable.Set.empty[BType]
      cnode.innerClasses.clear()

          def visitInternalName(value: String) {
            if(value == null) {
              return
            }
            var bt = lookupRefBType(value)
            if (bt.isArray) {
              bt = bt.getElementType
            }
            if(bt.hasObjectSort && !bt.isPhantomType && (bt != BoxesRunTime)) {
              if(exemplars.get(bt).isInnerClass) {
                refedInnerClasses += bt
              }
            }
          }

          def visitDescr(desc: String) {
            val bt = descrToBType(desc)
            if(bt.isArray) { visitDescr(bt.getElementType.getDescriptor) }
            else if(bt.sort == BType.METHOD) {
              visitDescr(bt.getReturnType.getDescriptor)
              bt.getArgumentTypes foreach { at => visitDescr(at.getDescriptor) }
            } else if(bt.hasObjectSort) {
              visitInternalName(bt.getInternalName)
            }
          }

      visitInternalName(cnode.name)
      visitInternalName(cnode.superName)
      JListWrapper(cnode.interfaces) foreach visitInternalName
      visitInternalName(cnode.outerClass)
      JListWrapper(cnode.fields)  foreach { fn: FieldNode  => visitDescr(fn.desc) }
      JListWrapper(cnode.methods) foreach { mn: MethodNode => visitDescr(mn.desc) }

      // annotations not visited because they store class names in CONSTANT_Utf8_info as opposed to the CONSTANT_Class_info that matter for InnerClasses.

      // TODO JDK8 the BootstrapMethodsAttribute may point via bootstrap_arguments to one or more CONSTANT_Class_info entries

      for(m <- JListWrapper(cnode.methods)) {

        JListWrapper(m.exceptions) foreach visitInternalName

        JListWrapper(m.tryCatchBlocks) foreach { tcb => visitInternalName(tcb.`type`) }

        val iter = m.instructions.iterator()
        while(iter.hasNext) {
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

    }

    //--------------------------------------------------------------------
    // First optimization pack
    //--------------------------------------------------------------------

    /**
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
    def cleanseMethod(cName: String, mnode: asm.tree.MethodNode): Boolean = {

      var changed = false
      var keepGoing = false

      do {
        keepGoing = false

        jumpsCollapser.transform(mnode)            // collapse a multi-jump chain to target its final destination via a single jump
        keepGoing |= jumpsCollapser.changed
        repOK(mnode)

        unreachCodeRemover.transform(cName, mnode) // remove unreachable code
        keepGoing |= unreachCodeRemover.changed
        repOK(mnode)

        labelsCleanup.transform(mnode)             // remove those LabelNodes and LineNumbers that aren't in use
        keepGoing |= labelsCleanup.changed
        repOK(mnode)

        danglingExcHandlers.transform(mnode)
        keepGoing |= danglingExcHandlers.changed
        repOK(mnode)

        changed |= keepGoing

      } while (keepGoing)

      changed

    }

    //--------------------------------------------------------------------
    // Second optimization pack
    //--------------------------------------------------------------------

    /**
     *  This method performs a few intra-method optimizations,
     *  aimed at reverting the extra copying introduced by inlining:
     *    - replace the last link in a chain of data accesses by a direct access to the chain-start.
     *    - dead-store elimination
     *    - remove those (producer, consumer) pairs where the consumer is a DROP and
     *      the producer has its value consumed only by the DROP in question.
     *
     * */
    def elimRedundantCode(cName: String, mnode: asm.tree.MethodNode): Boolean = {
      var changed   = false
      var keepGoing = false

      do {

        keepGoing = false

        copyPropagator.transform(cName, mnode) // replace the last link in a chain of data accesses by a direct access to the chain-start.
        keepGoing |= copyPropagator.changed

        deadStoreElim.transform(cName, mnode)  // replace STOREs to non-live local-vars with DROP instructions.
        keepGoing |= deadStoreElim.changed

        ppCollapser.transform(cName, mnode)    // propagate a DROP to the instruction(s) that produce the value in question, drop the DROP.
        keepGoing |= ppCollapser.changed

        jumpReducer.transform(mnode)           // simplifies branches that need not be taken to get to their destination.
        keepGoing |= jumpReducer.changed

        changed = (changed || keepGoing)

      } while (keepGoing)

      changed
    }

    //--------------------------------------------------------------------
    // Third optimization pack: Repeatable reads
    //--------------------------------------------------------------------

    /**
     *  A common idiom emitted by explicitouter and lambdalift involves
     *  dot navigation rooted at a local (for example, LOAD 0)
     *  followed by invocations of one or more getters or GETFIELD each of which isStable.
     *  The result of that access-path is a value that depends only on the access path,
     *  where the access path behaves as "repeatable read".
     *
     *  Rather than duplicating the access path each time the value in question is required,
     *  that value can be stored after its first access in a local-var added for that purpose.
     *  This way, any side-effects required upon first access (e.g. lazy-val initialization)
     *  are preserved, while successive accesses load a local (shorter code size, faster).
     *
     *  Method `cacheRepeatableReads()` injects caching code in four steps:
     *
     *    (1) A dataflow-analysis (realized by `StableChainAnalyzer` and `StableChainInterpreter`)
     *        associates a (for now virtual) local var to each prefix of an access-path,
     *        in effect a form of Unique Value Numbering. The dataflow-analysis determines
     *        those callsites that finish a prefix (in particular, to really be a prefix,
     *        the same stable-value must reach the callsite over all control-flow paths).
     *
     *    (2) So far the list of instructions hasn't been changed in any way,
     *        because the unique-value-numbering above doesn't discriminate
     *        whether an access-path "is seen for the first time" (and should be cached)
     *        or not (thus the cached value is available and should be used instead).
     *        This step takes a conservative approach, and "always caches",
     *        inserting a STORE-LOAD for the unique variable for that access path
     *        (even if it was already available, this will be fixed later).
     *
     *        `StableChainInterpreter` represents the unique-value-numbering in a form useful for Steps (2) and (3):
     *
     *          // maps an instruction that pushes a StableValue to THE local that caches method-wide that StableValue
     *          val candidates = scala.collection.mutable.Map.empty[MethodInsnNode, Int]
     *
     *    (3) Those callsites for which an already-cached stable-value is cached yet again, are elided.
     *        In order to determine when a stable-value expression is available (ie "already-cached")
     *        a Definite Assignment Analysis is used (realized by `DefinitelyAnalyzer` and `DefinitelyInterpreter`).
     *        Eliding involves:
     *
     *          (3.a) deleting the follow-up STORE but leaving the follow-up LOAD;
     *          (3.b) replacing the callsite with a DROP, to pop the receiver of the callsite
     *
     *    (4) After the above, most redundant access-paths are gone away.
     *        Three standard optimizers are run (push-pop collapser, dead-store elimination,
     *        and eliding of unused local vars) to emit more compact code.
     *
     * TODO 1: This optimization is always applied even though there's a treshold under which
     *         it increases by 1 the instruction count (a stable value accessed twice over a single hop).
     *         Still, the resulting code shouldn't be slower.
     *
     * TODO 2: STORE-LOAD right before a tableswitch is considered non-elidable by DeadStoreElim
     *
     * TODO 3: Stable-values accessed only via getters are taken into account, unlike those via GETFIELD or GETSTATIC.
     *
     */
    def cacheRepeatableReads(cName: String, mnode: asm.tree.MethodNode) {

      import asm.tree.analysis.Frame

      val insnCountOnEntry = mnode.instructions.size() // debug

      // ---------------------- Step (1) ----------------------

      val sci = new StableChainInterpreter(mnode)
      val sca = new StableChainAnalyzer(mnode, sci)
      sca.analyze(cName, mnode)

      // those links of an access-path that are accessed just once need not be cached
      /*
      val bins = interpreter.candidates.groupBy( { case Pair(callsite, idx) => idx } )
      for(bin <- bins; if bin._2.size == 1; Pair(callsite, _) <- bin._2) {
        interpreter.candidates.remove(callsite)
      }
      */
      if(sci.candidates.isEmpty) {
        return
      }

      // ---------------------- Step (2) ----------------------

      mnode.maxLocals = sci.nxtFreeLocalIdx

      for (Pair(callsite, idx) <- sci.candidates) {
        val t  = BType.getReturnType(callsite.desc)
        val st = new asm.tree.VarInsnNode(t.getOpcode(Opcodes.ISTORE), idx)
        val ld = new asm.tree.VarInsnNode(t.getOpcode(Opcodes.ILOAD),  idx)
        // after inserting or removing instructions, frameAt() doesn't work because Analyzer.frames doesn't know about the added insns.
        mnode.instructions.insert(callsite, ld)
        mnode.instructions.insert(callsite, st)
      }

      // ---------------------- Step (3) ----------------------

      // Definite Assignment analysis
      val dai = new DefinitelyInterpreter(sci.uniqueValueInv)
      val daa = new DefinitelyAnalyzer(dai)
      daa.analyze(cName, mnode)

      val cachedFrames = (
        for(Pair(callsite, idx) <- sci.candidates)
        yield (callsite -> daa.frameAt(callsite).asInstanceOf[Frame[SourceValue]])
      ).toMap

      for (Pair(callsite, idx) <- sci.candidates) {
        val frame = cachedFrames(callsite)
        val sv    = frame.getLocal(idx)
        if(dai.isDefinitelyAssigned(sv)) {

          assert(Util.isSTORE(callsite.getNext))
          val st = callsite.getNext.asInstanceOf[VarInsnNode]
          assert(st.`var` == idx)

          mnode.instructions.remove(callsite.getNext)

          val stackTop = frame.getStackTop
          val rcvSize  = stackTop.getSize
          assert(rcvSize == 1)
          mnode.instructions.insert(callsite, Util.getDrop(rcvSize))

          mnode.instructions.remove(callsite)
        }
      }

      // ---------------------- Step (4) ----------------------

      ppCollapser.transform(cName, mnode)    // propagate a DROP to the instruction(s) that produce the value in question, drop the DROP.
      deadStoreElim.transform(cName, mnode)  // replace STOREs to non-live local-vars with DROP instructions.
      lvCompacter.transform(mnode)           // compact local vars, remove dangling LocalVariableNodes.

      val insnCountOnExit = mnode.instructions.size() // debug

      /*
      if(insnCountOnExit > insnCountOnEntry) {
        println("Added " + (insnCountOnExit - insnCountOnEntry) + " in class " + cName + " , method " + mnode.name + mnode.desc)
      } else if(insnCountOnExit < insnCountOnEntry) {
        println("Subtracted " + (insnCountOnEntry - insnCountOnExit) + " in class " + cName + " , method " + mnode.name + mnode.desc)
      }
      */

    }

    /**
     *  Definite Assignment analysis. See `DefinitelyInterpreter`
     */
    class DefinitelyAnalyzer(dint: DefinitelyInterpreter)
    extends asm.tree.analysis.Analyzer(dint) {

      override def newNonFormalLocal(idx: Int): SourceValue = {
        dint.uniqueValueInv.get(idx) match {
          case Some(uv) => dint.unassigneds(uv.link.getSize)
          case _        => super.newNonFormalLocal(idx)
        }
      }

    }

    /**
     *  Interpreter for a Definite Assignment analysis. See `DefinitelyAnalyzer`
     */
    class DefinitelyInterpreter(val uniqueValueInv: scala.collection.Map[Int, UniqueValueKey])
    extends asm.tree.analysis.SourceInterpreter {

      val unassigneds: Array[SourceValue] = Array(
        null,
        unAssignedValue(1),
        unAssignedValue(2)
      )

      private def unAssignedValue(size: Int): SourceValue = {
        val fake = new UnBoxAnalyzer.FakeParamLoad(-1, null, false)
        new SourceValue(size, fake)
      }

      def isDefinitelyAssigned(sv: SourceValue): Boolean = {
        if(sv.insns.isEmpty()) {
          return false
        }
        val iter = sv.insns.iterator()
        while(iter.hasNext()) {
          if(iter.next().isInstanceOf[UnBoxAnalyzer.FakeInsn]) {
            return false
          }
        }

        true
      }

      override def copyOperation(insn: asm.tree.AbstractInsnNode, value: SourceValue): SourceValue = {
        insn.getOpcode match {
          case Opcodes.ISTORE |
               Opcodes.FSTORE |
               Opcodes.ASTORE => new SourceValue(1, insn) // kills previous (possibly not-definitely-assigned) value
          case Opcodes.LSTORE |
               Opcodes.DSTORE => new SourceValue(2, insn) // kills previous (possibly not-definitely-assigned) value
          case _ =>
            value // propagates the (possibly not-definitely-assigned) value
        }
      }

      override def newValue(ctype: asm.Type): SourceValue = {
        if      (ctype == asm.Type.VOID_TYPE) { null }
        else if (ctype == null)               { unassigneds(1) }
        else                                  { unassigneds(ctype.getSize()) }
      }

    }

    class StableChainAnalyzer(mnode: asm.tree.MethodNode, interpreter: StableChainInterpreter)
    extends asm.tree.analysis.Analyzer(interpreter) {

      // Those params never assigned qualify as "stable-roots" for "stable-access-paths"
      // Code that has been tail-call-transformed contains assignments to formals.
      val stableLocals = {
        val stableLocals = new Array[Boolean](descrToBType(mnode.desc).getArgumentCount)
        var idx = 0
        while(idx < stableLocals.length) {
          stableLocals(idx) = true
          idx += 1
        }
        val insns = mnode.instructions.toArray
        for (insn <- insns if insn != null) {
          if (asm.optimiz.Util.isSTORE(insn)) {
            val st = insn.asInstanceOf[asm.tree.VarInsnNode]
            if (st.`var` < stableLocals.length) {
              stableLocals(st.`var`) = false
            }
          }
        }

        stableLocals
      }

      override def newFormal(isInstanceMethod: Boolean, idx: Int, ctype: asm.Type): StableValue = {
        if ((idx < stableLocals.length) && stableLocals(idx)) StableValue(idx, ctype.getSize)
        else interpreter.dunno(ctype.getSize)
      }

    }

    /**
     *  Represents *an individual link* in an access-path all whose links are stable.
     *  Such access-path is a lattice element in the StableChainInterpreter dataflow-analysis.
     *
     *  Rather than representing it as chain, a more compact way leverages the property that
     *  each prefix of one such access-path is associated to a unique local (ie, a form of "unique value numbering").
     *  An access-path `P` can be expressed as `P.init` . `P.last`, which in turn is mapped to a unique local.
     *
     *  @param index unique local (as in "unique value numbering") denoting this stable access-path
     *  @param vsize whether the resulting value is a category-1 or category-2 JVM type.
     */
    case class StableValue(index: Int, vsize: Int) extends asm.tree.analysis.Value {
      override def getSize() = vsize
      def isStable = (index != -1)
    }

    case class UniqueValueKey(prefixIndex: Int, link: StableMember)

    class StableChainInterpreter(mnode: asm.tree.MethodNode) extends asm.tree.analysis.Interpreter[StableValue](asm.Opcodes.ASM4) {

      private val UNKNOWN_1 = StableValue(-1, 1)
      private val UNKNOWN_2 = StableValue(-1, 2)

      val dunno = Array[StableValue](null, UNKNOWN_1, UNKNOWN_2)

      private def dunno(producer: asm.tree.AbstractInsnNode): StableValue = {
        dunno(asm.optimiz.SizingUtil.getResultSize(producer))
      }

      var nxtFreeLocalIdx = mnode.maxLocals
      val uniqueValue     = scala.collection.mutable.Map.empty[UniqueValueKey, Int]
      val uniqueValueInv  = scala.collection.mutable.Map.empty[Int, UniqueValueKey]

      // maps an instruction that pushes a StableValue to THE local that caches method-wide that StableValue
      val candidates = scala.collection.mutable.Map.empty[MethodInsnNode, Int]

      private def getUniqueValueNumbering(prefixIndex: Int, link: StableMember): StableValue = {
        val size = link.getSize

        var index = -1
        uniqueValue.get(UniqueValueKey(prefixIndex, link)) match {
          case Some(existing) =>
            index = existing
          case _ =>
            index   = nxtFreeLocalIdx
            val uvk = UniqueValueKey(prefixIndex, link)
            uniqueValue   .put(uvk, index)
            uniqueValueInv.put(index, uvk)
            nxtFreeLocalIdx += size
        }

        StableValue(index, size)
      }

      override def newValue(t: asm.Type) = {
        if (t == asm.Type.VOID_TYPE) null
        else if (t == null) null
        else dunno(t.getSize())
      }

      /**
       * ACONST_NULL,
       * ICONST_M1, ICONST_0, ICONST_1, ICONST_2, ICONST_3, ICONST_4, ICONST_5,
       * LCONST_0, LCONST_1,
       * FCONST_0, FCONST_1, FCONST_2,
       * DCONST_0, DCONST_1,
       * BIPUSH,   SIPUSH,
       * LDC,
       * JSR,
       * GETSTATIC, // TODO
       * NEW
       */
      override def newOperation(insn: asm.tree.AbstractInsnNode) = { dunno(insn) }

      /**
       * Propagates the input value through LOAD, STORE, DUP, and SWAP instructions.
       */
      override def copyOperation(insn: asm.tree.AbstractInsnNode, value: StableValue) = { value }

      /**
       * INEG, LNEG, FNEG, DNEG,
       * IINC,
       *       I2L, I2F, I2D,
       * L2I,      L2F, L2D,
       * F2I, F2L,      F2D,
       * D2I, D2L, D2F,
       * I2B, I2C, I2S
       *
       * IFEQ, IFNE, IFLT, IFGE, IFGT, IFLE,
       * IFNULL, IFNONNULL
       * TABLESWITCH, LOOKUPSWITCH,
       * IRETURN, LRETURN, FRETURN, DRETURN, ARETURN,
       * PUTSTATIC,
       * GETFIELD, // TODO
       * NEWARRAY, ANEWARRAY, ARRAYLENGTH,
       * ATHROW,
       * CHECKCAST, INSTANCEOF,
       * MONITORENTER, MONITOREXIT,
       */
      override def unaryOperation(insn: asm.tree.AbstractInsnNode, value: StableValue) = {
        // Actually some unaryOperation on a stable-value results in another stable-value,
        // but to keep things simple this operation is considered to finish a stable-access-path
        // ("to keep things simple" means: the only way to extend an stable-access-path is via a "stable" INVOKE or GETFIELD)
        dunno(insn)
      }

      /**
       * IADD, LADD, FADD, DADD,
       * ISUB, LSUB, FSUB, DSUB,
       * IMUL, LMUL, FMUL, DMUL,
       * IDIV, LDIV, FDIV, DDIV,
       * IREM, LREM, FREM, DREM,
       * ISHL, LSHL,
       * ISHR, LSHR,
       * IUSHR, LUSHR,
       * IAND, LAND,
       * IOR, LOR,
       * IXOR, LXOR,
       * LCMP,
       * FCMPL, FCMPG,
       * DCMPL, DCMPG,
       * IALOAD, LALOAD, FALOAD, DALOAD, AALOAD, BALOAD, CALOAD, SALOAD,
       * IF_ICMPEQ, IF_ICMPNE, IF_ICMPLT, IF_ICMPGE, IF_ICMPGT, IF_ICMPLE,
       * IF_ACMPEQ, IF_ACMPNE,
       * PUTFIELD
       */
      override def binaryOperation(insn: asm.tree.AbstractInsnNode, value1: StableValue, value2: StableValue) = {
        // Actually some binaryOperations on two stable-values results in another stable-value,
        // but to keep things simple this operation is considered to finish a stable-access-path
        // ("to keep things simple" means: the only way to extend an stable-access-path is via a "stable" INVOKE or GETFIELD)
        dunno(insn)
      }

      /**
       * IASTORE, LASTORE, FASTORE, DASTORE, AASTORE, BASTORE, CASTORE, SASTORE
       */
      override def ternaryOperation(
        insn:   asm.tree.AbstractInsnNode,
        value1: StableValue,
        value2: StableValue,
        value3: StableValue) = {
        dunno(insn)
      }

      /**
       * INVOKEVIRTUAL, INVOKESPECIAL, INVOKESTATIC, INVOKEINTERFACE,
       * MULTIANEWARRAY and INVOKEDYNAMIC
       */
      override def naryOperation(insn: asm.tree.AbstractInsnNode, values: java.util.List[_ <: StableValue]): StableValue = {
        insn.getOpcode match {

          case Opcodes.INVOKEVIRTUAL
             | Opcodes.INVOKESPECIAL
             | Opcodes.INVOKEINTERFACE if values.size() == 1 && values.get(0).isStable =>

            val stableRcv  = values.get(0)
            val callsite   = insn.asInstanceOf[MethodInsnNode]
            val owner      = lookupRefBType(callsite.owner)
            val memberName = callsite.name
            val memberType = descrToBType(callsite.desc)
            val link       = StableMember(owner, memberName, memberType)

            if (repeatableReads.contains(link)) {
              val sv = getUniqueValueNumbering(stableRcv.index, link)
              candidates.get(callsite) match {
                case Some(existingIdx) => assert(existingIdx == sv.index)
                case None => candidates.put(callsite, sv.index)
              }
              sv
            } else {
              candidates.remove(callsite)
              dunno(memberType.getReturnType.getSize)
            }

          case Opcodes.INVOKESTATIC    => dunno(insn)

          case Opcodes.INVOKEDYNAMIC   => dunno(insn)

          case _                       => dunno(insn)
        }
      }

      /**
       * IRETURN, LRETURN, FRETURN, DRETURN, ARETURN
       */
      override def returnOperation(insn: asm.tree.AbstractInsnNode, value: StableValue, expected: StableValue) { }

      /**
       * POP, POP2
       */
      override def drop(insn: asm.tree.AbstractInsnNode, value: StableValue) { }

      override def merge(d: StableValue, w: StableValue) = {
        if(d == null) w
        else if (w == null) d
        else {
          assert(d.getSize() == w.getSize())
          if (d == w) d else dunno(d.getSize())
        }
      }

    } // end of class StableChainInterpreter

    //--------------------------------------------------------------------
    // Type-flow analysis
    //--------------------------------------------------------------------

    def runTypeFlowAnalysis(owner: String, mnode: MethodNode) {

      import asm.tree.analysis.{ Analyzer, Frame }
      import asm.tree.AbstractInsnNode

      val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
      tfa.analyze(owner, mnode)
      val frames: Array[Frame[TFValue]]   = tfa.getFrames()
      val insns:  Array[AbstractInsnNode] = mnode.instructions.toArray()
      var i = 0
      while(i < insns.length) {
        if (frames(i) == null && insns(i) != null) {
          // TODO assert(false, "There should be no unreachable code left by now.")
        }
        i += 1
      }
    }

    //--------------------------------------------------------------------
    // Utilities for reuse by different optimizers
    //--------------------------------------------------------------------

    /**
     *  Well-formedness checks, useful after each fine-grained transformation step on a MethodNode.
     *
     *  Makes sure that exception-handler and local-variable entries are non-obviously wrong
     *  (e.g., the left and right brackets of instruction ranges are checked, right bracket should follow left bracket).
     */
    def repOK(mnode: asm.tree.MethodNode): Boolean = {
      if(!global.settings.debug.value) {
        return true;
      }

          def isInsn(insn: asm.tree.AbstractInsnNode) {
            assert(mnode.instructions.contains(insn))
          }

          def inSequence(fst: asm.tree.AbstractInsnNode, snd: asm.tree.AbstractInsnNode): Boolean = {
            var current = fst
            while(true) {
              current = current.getNext()
              if(current == null) { return false }
              if(current == snd)  { return true  }
            }
            false
          }

      val insnIter = mnode.instructions.iterator()
      while(insnIter.hasNext) {
        assert(insnIter.next() != null, "instruction stream shouldn't contain nulls.")
      }

      // exception-handler entries
      if(mnode.tryCatchBlocks != null) {
        val tryIter = mnode.tryCatchBlocks.iterator()
        while(tryIter.hasNext) {
          val tcb = tryIter.next
          assert(tcb.start   != null)
          assert(tcb.end     != null)
          assert(tcb.handler != null)
          isInsn(tcb.start)
          isInsn(tcb.end)
          isInsn(tcb.handler)
          inSequence(tcb.start, tcb.end)
        }
      }

      // local-vars entries
      if(mnode.localVariables != null) {
        val lvIter = mnode.localVariables.iterator()
        while(lvIter.hasNext) {
          val lv = lvIter.next
          isInsn(lv.start)
          isInsn(lv.end)
          inSequence(lv.start, lv.end)
        }
      }

      true
    }

  } // end of class BCodeCleanser

  //--------------------------------------------------------
  // Optimization pack: Method-inlining and Closure-inlining
  //--------------------------------------------------------

  /**
   * Each MethodNode built for a plain class is inspected for callsites targeting @inline methods,
   * those callsites are collected in a `CallGraphNode` instance,
   * classified into "higher-order callsites" (ie taking one or more functions as arguments) and the rest.
   *
   * The callsites in question constitute "requests for inlining". An attempt will be made to fulfill them,
   * after breaking any inlining cycles. Moreover a request may prove unfeasible afterwards too,
   * e.g. due to the callsite program point having a deeper operand-stack than the arguments the callee expects,
   * and the callee contains exception handlers).
   *
   * A description of the workflow for method-inlining and closure-inlining can be found in `WholeProgramAnalysis.inlining()`.
   *
   * @param hostOwner the JVM-level class defining method host
   *
   * @param host the method were inlining has been requested
   *
   */
  final class CallGraphNode(val hostOwner: ClassNode, val host: MethodNode) {

    var hiOs:  List[InlineTarget] = Nil
    var procs: List[InlineTarget] = Nil

    def isEmpty    = (hiOs.isEmpty && procs.isEmpty)
    def candidates = (hiOs ::: procs).sorted(inlineTargetOrdering)

    /** can-multi-thread, provided each callsite.owner has been entered as TypeName in Names */
    def populate() {
      if(!Util.isReadyForAnalyzer(host)) {
        Util.computeMaxLocalsMaxStack(host)
      }
      for(c <- candidates) {
        val callsite = c.callsite
        val ownerBT = lookupRefBType(callsite.owner)
        // `null` usually indicates classfile wasn't found and thus couldn't be parsed. TODO warning?
        val mnAndOwner = codeRepo.getMethodOrNull(ownerBT, callsite.name, callsite.desc)
        c.setMethodAndOwner(mnAndOwner)
        if(c.callee != null && !Util.isReadyForAnalyzer(c.callee)) {
          Util.computeMaxLocalsMaxStack(c.callee)
        }
      }
      hiOs  = hiOs  filter { it => it.callee != null }
      procs = procs filter { it => it.callee != null }
    }

    def isRepOK: Boolean = {
      candidates forall { c => c.callee != host } // non-cyclic
    }

  }

  object cgnOrdering extends scala.math.Ordering[CallGraphNode] {
    def compare(x: CallGraphNode, y: CallGraphNode): Int = {
      var result = x.host.instructions.size().compare(y.host.instructions.size())
      if (result == 0) {
        result = x.hashCode().compare(y.hashCode())
      }
      result
    }
  }

  final class InlineTarget(val callsite: MethodInsnNode) {
    var callee: MethodNode = null
    var owner:  ClassNode  = null

    def setMethodAndOwner(mnAndOwner: MethodNodeAndOwner) {
      if(mnAndOwner == null) {
        callee = null
        owner  = null
      }
      else {
        callee = mnAndOwner.mnode
        owner  = mnAndOwner.owner
      }
    }
  }

  object inlineTargetOrdering extends scala.math.Ordering[InlineTarget] {
    def compare(x: InlineTarget, y: InlineTarget): Int = {
      x.hashCode().compare(y.hashCode())
    }
  }

  object codeRepo {

    val parsed  = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]
    val classes = new java.util.concurrent.ConcurrentHashMap[BType, asm.tree.ClassNode]

    def containsKey(bt: BType): Boolean = {
      val res = (classes.containsKey(bt) || parsed.containsKey(bt))

      res
    }

    def getFieldOrNull(bt: BType, name: String, desc: String): FieldNode = {
      try { getField(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the FieldInsnNode have compiled?
      }
    }

    def getMethodOrNull(bt: BType, name: String, desc: String): MethodNodeAndOwner = {
      try { getMethod(bt, name, desc) }
      catch {
        case ex: MissingRequirementError =>
          null // TODO bytecode parsing shouldn't fail, otherwise how could the callsite have compiled?
      }
    }

    /**
     * Looks up (parsing from bytecode if needed) the field declared in `bt`
     * given by the combination of field-name and field-descriptor.
     *
     * must-single-thread
     */
    def getField(bt: BType, name: String, desc: String): FieldNode = {
      val cn = getClassNode(bt)
      val iter = cn.fields.iterator()
      while(iter.hasNext) {
        val fn = iter.next()
        if(fn.name == name && fn.desc == desc) {
          return fn
        }
      }

      MissingRequirementError.notFound("Could not find FieldNode: " + bt.getInternalName + "." + name + ": " + desc)
    }

    /**
     * Looks up (parsing from bytecode if needed) the method declared in `bt`
     * given by the combination of method-name and method-descriptor.
     * Keeps looking up over the superclass hierarchy, until reaching j.l.Object
     *
     * @return if found, the MethodNode and the ClassNode declaring it. Otherwise MissingRequirementError is thrown.
     *
     * must-single-thread
     */
    def getMethod(bt: BType, name: String, desc: String): MethodNodeAndOwner = {

      var current = bt

      while(current != null) {
        val cn = getClassNode(current)
        val iter = cn.methods.iterator()
        while(iter.hasNext) {
          val mn = iter.next()
          if(mn.name == name && mn.desc == desc) {
            return MethodNodeAndOwner(mn, cn)
          }
        }
        current = if(cn.superName == null) null else lookupRefBType(cn.superName)
      }

      MissingRequirementError.notFound("Could not find MethodNode: " + bt.getInternalName + "." + name + desc)
    }

    /** must-single-thread */
    def getClassNode(owner: String): asm.tree.ClassNode = {
      getClassNode(brefType(owner))
    }

    /**
     *  Returns the ASM ClassNode for a class that's being compiled or that's going to be parsed from external bytecode.
     *
     *  After this method has run, the following two post-conditions hold:
     *    - `exemplars.containsKey(bt)`
     *    - `codeRepo.containsKey(bt)`
     *
     *  must-single-thread
     */
    def getClassNode(bt: BType): asm.tree.ClassNode = {
      var res = classes.get(bt)
      if(res == null) {
        res = parsed.get(bt)
        if(res == null) {
          res = parseClassAndEnterExemplar(bt)
        }
      }
      assert(exemplars.containsKey(bt))
      res
    }

    /**
     *  A few analyses (e.g., Type-Flow Analysis) require `exemplars` to contain entries for all classes the analysis encounters.
     *  A class that's being compiled in this is already associated to a Tracked instance (GenBCode took care of that).
     *  For a class `bt` mentioned in external bytecode, this method takes care of creating the necessary entry in `exemplars`.
     *
     *  After this method has run the following two post-conditions hold:
     *    - `exemplars.containsKey(bt)`
     *    - `codeRepo.parsed.containsKey(bt)`
     *
     *  @param bt a "normal" class (see `BType.isNonSpecial`) for which an entry in `exemplars` should be added if not yet there.
     *
     *  @return   the ASM ClassNode after parsing the argument from external bytecode.
     *
     *  must-single-thread
     */
    def parseClassAndEnterExemplar(bt: BType): ClassNode = {
      assert(bt.isNonSpecial, "The `exemplars` map is supposed to hold ''normal'' classes only, not " + bt.getInternalName)
      assert(!containsKey(bt),   "codeRepo already contains " + bt.getInternalName)

          /** must-single-thread */
          def parseClass(): asm.tree.ClassNode = {
            assert(!containsKey(bt))
            val iname   = bt.getInternalName
            val dotName = iname.replace('/', '.')
            classPath.findSourceFile(dotName) match {
              case Some(classFile) =>
                val cn = new asm.tree.ClassNode()
                val cr = new asm.ClassReader(classFile.toByteArray)
                cr.accept(cn, asm.ClassReader.SKIP_FRAMES)
                parsed.put(bt, cn)
                cn
              case _ => MissingRequirementError.notFound("Could not find bytecode for " + dotName)
            }
          }

      val cn = parseClass()

      if(exemplars.containsKey(bt)) {
        return cn // TODO check if superName, interfaces, etc agree btw cn and exemplar(bt)
      }

          def enterIfUnseen(iname: String): Tracked = {
            val bt = brefType(iname)
            var exempl = exemplars.get(bt)
            if(exempl == null) {
              parseClassAndEnterExemplar(bt)
              exempl = exemplars.get(bt)
            }
            exempl
          }

          def enterIfUnseens(inames: java.util.List[String]): Array[Tracked] = {
            var ifaces: List[Tracked] = Nil
            val iter = inames.iterator()
            while(iter.hasNext) {
              ifaces ::= enterIfUnseen(iter.next())
            }
            if(ifaces.isEmpty) { EMPTY_TRACKED_ARRAY }
            else {
              val arr = new Array[Tracked](ifaces.size)
              ifaces.copyToArray(arr)
              arr
            }
          }

      val tsc       = enterIfUnseen(cn.superName)
      val ifacesArr = enterIfUnseens(cn.interfaces)

      // ClassNode.innerClasses isn't indexed by InnerClassNode.name, this map accomplishes that feat.
      val innerClassNode: Map[String, InnerClassNode] = {
        JListWrapper(cn.innerClasses) map (icn => (icn.name -> icn)) toMap
      }

      val isInnerClass = innerClassNode.contains(cn.name)
      val innersChain: Array[InnerClassEntry] =
        if(!isInnerClass) null
        else {

              def toInnerClassEntry(icn: InnerClassNode): InnerClassEntry = {
                InnerClassEntry(icn.name, icn.outerName, icn.innerName, icn.access)
              }

          var chain: List[InnerClassEntry] = toInnerClassEntry(innerClassNode(cn.name)) :: Nil
          var keepGoing = true
          do {
            // is the enclosing class of the current class itself an inner class?
            val currentOuter = chain.head.outerName
            keepGoing = innerClassNode.contains(currentOuter)
            if(keepGoing) {
              chain ::= toInnerClassEntry(innerClassNode(currentOuter))
            }
          } while(keepGoing)

          chain.toArray
        }

      val tr = Tracked(bt, cn.access, tsc, ifacesArr, innersChain)
      exemplars.put(tr.c, tr) // no counterpart in symExemplars, that's life.

      cn
    }

    /**
     *  An invariant we want to maintain:
     *    "each internal name mentioned in an instruction that's part of this program
     *     should have a Tracked instance (which implies, a BType instance)"
     *  That invariant guarantees a Type-Flow Analysis can be run anytime, which might be useful.
     *
     *  This method goes over its argument looking for not-yet-seen TypeNames,
     *  fabricating a Tracked instance for them (if needed by parsing bytecode,
     *  thus the location of this method as utility in codeRepo).
     *
     *  Without a TypeName for an internal name or method descriptor, the following conversions can't be performed:
     *    from type-descriptor to BType, via `BCodeTypes.descrToBType()`
     *    from internal-name   to BType, via `BCodeTypes.lookupRefBType()`
     *  In turn, BTypes are indispensable as keys to the `exemplars` map.
     *
     *  must-single-thread
     */
    def enterExemplarsForUnseenTypeNames(insns: InsnList) {

        def enterInternalName(iname: String) {
          var bt = brefType(iname)
          if(bt.isArray) {
            bt = bt.getElementType
          }
          if(bt.isNonSpecial && !exemplars.containsKey(bt)) {
            codeRepo.parseClassAndEnterExemplar(bt)
          }
        }

        def enterDescr(desc: String) {
          val c: Char = desc(0)
          c match {
            case 'V' | 'Z' | 'C' | 'B' | 'S' | 'I' | 'F' | 'J' | 'D' => ()
            case 'L' =>
              val iname = desc.substring(1, desc.length() - 1)
              enterInternalName(iname)
            case '(' =>
              val mt = BType.getMethodType(desc)
              enterDescr(mt.getReturnType.getDescriptor)
              for(argt <- mt.getArgumentTypes) {
                enterDescr(argt.getDescriptor)
              }
            case '[' =>
              val arrt = BType.getType(desc)
              enterDescr(arrt.getComponentType.getDescriptor)
          }
        }

      val iter = insns.iterator()
      while(iter.hasNext) {
        val insn = iter.next()
        insn match {
          case ti: TypeInsnNode   => enterInternalName(ti.desc) // an intenal name, actually
          case fi: FieldInsnNode  => enterInternalName(fi.owner); enterDescr(fi.desc)
          case mi: MethodInsnNode => enterInternalName(mi.owner); enterDescr(mi.desc)
          case ivd: InvokeDynamicInsnNode => () // TODO
          case ci: LdcInsnNode =>
            ci.cst match {
              case t: asm.Type => enterDescr(t.getDescriptor)
              case _           => ()
            }
          case ma: MultiANewArrayInsnNode => enterDescr(ma.desc)
          case _ => ()
        }
      }

    } // end of method enterExemplarsForUnseenTypeNames()

    def clear() {
      parsed.clear()
      classes.clear()
    }

  } // end of object codeRepo

  /**
   * Whole-program analyses can be performed right after classfiles are in q2,
   * but before letting the intra-method optimizations loose on them we do the inter-procedural ones.
   */
  class WholeProgramAnalysis {

    import asm.tree.analysis.{Analyzer, BasicValue, BasicInterpreter}

    /**
     *  Performs closure-inlining and method-inlining, by first breaking any cycles over the "inlined-into" relation (see `object dagset`).
     *  Afterwards, method-inlining is done in:
     *     def inlineMethod(ha: Analyzer[BasicValue], host: MethodNode, callsite: MethodInsnNode, callee: MethodNode): Boolean
     *  And closure-inlining is done in:
     *     TODO
     */
    def inlining() {

      /*
       * The MethodNode for each callsite to an @inline method is found, if necessary by parsing bytecode
       * (ie the classfile given by a callsite's `owner` field).
       * Those classes can be parsed only after making sure they aren't being compiled in this run.
       * That's the case by now, in fact codeRepo.classes can't grow from now on.
       */
      val mn2cgn = mutable.Map.empty[MethodNode, CallGraphNode]
      for(cgn <- cgns) {
        cgn.populate()
        assert(cgn.isRepOK)
        mn2cgn += (cgn.host -> cgn)
      }
      /**
       *  Terminology:
       *    - host:   a method containing callsites for inlining
       *    - target: the method given by a callsite for inlining
       *
       *  `dagset` represents a set of DAGs with edges (target -> host)
       *  resulting from:
       *    (1) visiting all (host, targets) pairs collected during `GenBCode` in `BCodeOpt.cgns`,
       *    (2) adding to `dagset` a (target -> host) link unless doing so would establish a cycle.
       *
       *  Failure to add a link in (2) implies that `target` can't be inlined in `host`,
       *  thus the corresponding `InlineTarget` is removed from the `CallGraphNode` under consideration.
       *
       */
      object dagset extends mutable.HashMap[MethodNode, mutable.Set[MethodNode]] {

        /** true iff a link (target -> host) was added, false otherwise. */
        def linkUnlessCycle(target: MethodNode, host: MethodNode): Boolean = {
          val createsCycle = (this.contains(target) && isReachableFrom(target, host))
          val okToAdd = !createsCycle
          if(okToAdd) {
            val hosts = this.getOrElseUpdate(target, mutable.Set.empty)
            hosts += host
          }

          okToAdd
        }

        /** whether the first argument is reachable following zero or more links starting at the second argument. */
        def isReachableFrom(fst: MethodNode, snd: MethodNode): Boolean = {
          if(fst == snd) {
            return true
          }
          this.get(snd) match {
            case Some(nodes) => nodes exists { n => isReachableFrom(fst, n) } // there are no cycles, thus this terminates.
            case None        => false
          }
        }

      } // end of object dagset

      for(cgn <- cgns) {
        cgn.hiOs  = cgn.hiOs  filter { it: InlineTarget => dagset.linkUnlessCycle(it.callee, cgn.host) }
        cgn.procs = cgn.procs filter { it: InlineTarget => dagset.linkUnlessCycle(it.callee, cgn.host) }
      }

      /**
       *  It only remains to visit `cgns` in an order that ensures
       *  a CallGraphNode has stabilitzed (ie all inlinings have been performed inside it, with stable calees)
       *  by the time it's inlined in a host method.
       */
      val remaining = mutable.Set.empty[CallGraphNode]
      remaining ++= cgns.toList
      while(remaining.nonEmpty) {

        val leaves = remaining.filter( cgn => cgn.candidates.forall( c => !mn2cgn.contains(c.callee) || !remaining.contains(mn2cgn(c.callee)) ) )
        assert(leaves.nonEmpty, "Otherwise loop forever")

        for(leaf <- leaves) {
          val ha = new Analyzer[BasicValue](new BasicInterpreter)
          ha.analyze(leaf.hostOwner.name, leaf.host)
          // method-inlining
          leaf.procs foreach { proc =>
            // val before = Util.textify(leaf.host) // debug
            inlineMethod(ha, leaf.hostOwner.name, leaf.host, proc.callsite, proc.callee)
            ifDebug {
              val after = Util.textify(leaf.host)
              val da    = new Analyzer[BasicValue](new asm.tree.analysis.BasicVerifier)
              da.analyze(leaf.hostOwner.name, leaf.host)
            }
          }
          leaf.procs = Nil
          // closure-inlining
          leaf.hiOs foreach { hiO => /* TODO: closure-inlining */ }
          leaf.hiOs = Nil
        }

        remaining --= leaves
      }

    } // end of method inlining()

    /**
     * This method takes care of all the little details around inlining the callee's instructions for a callsite located in a `host` method.
     * Those details boil down to:
     *   (a) checking whether inlining is feasible. If unfeasible, don't touch anything and return false.
     *   (b) replacing the callsite with:
     *       STORE instructions for expected arguments,
     *       callee instructions adapted to their new environment
     *         (accesses to local-vars shifted,
     *          RETURNs replaced by jumps to the single-exit of the inlined instructions,
     *          without forgetting to empty all the stack slots except stack-top right before jumping)
     *   (c) copying over the debug info from the callee's
     *   (d) re-computing the maxLocals and maxStack of the host method.
     *   (e) return true.
     *
     * Inlining is considered unfeasible in two cases, summarized below and described in more detail on the spot:
     *   (a.1) due to the possibility of the callee clearing the operand-stack when entering an exception-handler, as well as
     *   (a.2) inlining would lead to illegal access errors.
     *
     * @param ha
     *           allows finding out the stack depth and stack-slot-sizes at the callsite of interest in the host method
     * @param hostOwner
     *                  the internal name of the class declaring the host method
     * @param host
     *             the method containing a callsite for which inlining has been requested
     * @param callsite
     *                 the invocation whose inlining is requested.
     *
     * @return
     *         true iff inlining was actually performed.
     *
     */
    private def inlineMethod(ha:        Analyzer[BasicValue],
                             hostOwner: String,
                             host:      MethodNode,
                             callsite:  MethodInsnNode,
                             callee:    MethodNode): Boolean = {

      assert(host.instructions.contains(callsite))
      assert(callee != null)
      assert(callsite.name == callee.name)
      assert(callsite.desc == callee.desc)

      /*
       * The first situation (a.1) under which method-inlining is unfeasible: In case both conditions below hold:
       *   (a.1.i ) the operand stack may be cleared in the callee, and
       *   (a.1.ii) the stack at the callsite in host contains more values than args expected by the callee.
       *
       * Alternatively, additional STORE instructions could be inserted to park those extra values while the inlined body executes,
       * but the overhead doesn't make it worth the effort.
       */
      if(!callee.tryCatchBlocks.isEmpty) {
        val stackHeight       = ha.frameAt(callsite).getStackSize
        val expectedArgs: Int = Util.expectedArgs(callsite)
        if(stackHeight > expectedArgs) {
          // TODO warning()
          return false
        }
        assert(stackHeight == expectedArgs)
      }

      // instruction cloning requires the following map to consistently replace new for old LabelNodes.
      val labelMap = Util.clonedLabels(callee)

      /*
       * In general callee.instructions and bodyInsns aren't same size,
       * for example because calleeInsns may contain FrameNodes which weren't cloned into body.
       * Therefore, don't try to match up original and cloned instructions by position!
       * Instead, `insnMap` is a safe way to find a cloned instruction using the original as key.
       */
      val insnMap   = new java.util.HashMap[AbstractInsnNode, AbstractInsnNode]()
      val body      = Util.clonedInsns(callee.instructions, labelMap, insnMap)
      val bodyInsns = body.toArray

      /*
       * In case the callee has been parsed from bytecode, its instructions may refer to type descriptors and internal names
       * that as of yet lack a corresponding TypeName in Names.chrs
       * (the GenBCode infrastructure standardizes on TypeNames for lookups.
       * The utility below takes care of creating TypeNames for those descriptors and internal names.
       * Even if inlining proves unfeasible, those TypeNames won't cause any harm.
       *
       * TODO why weren't those TypeNames entered as part of parsing callee from bytecode? After all, we might want to run e.g. Type-Flow Analysis on external methods before inlining them.
       */
      codeRepo.enterExemplarsForUnseenTypeNames(body)

      if(!allAccessesLegal(body, lookupRefBType(hostOwner))) {
        // TODO warning()
        return false
      }

      // By now it's a done deal that method-inlining will be performed. There's no going back.

      // each local-var access in `body` is shifted host.maxLocals places
      for(bodyInsn <- bodyInsns; if bodyInsn.getType == AbstractInsnNode.VAR_INSN) {
        val lvi = bodyInsn.asInstanceOf[VarInsnNode]
        lvi.`var` += host.maxLocals
      }

      val calleeMethodType = BType.getMethodType(callee.desc)

      // add a STORE instruction for each expected argument, including for THIS instance if any.
      val argStores   = new InsnList
      var nxtLocalIdx = host.maxLocals
      if(Util.isInstanceMethod(callee)) {
        argStores.insert(new VarInsnNode(Opcodes.ASTORE, nxtLocalIdx))
        nxtLocalIdx    += 1
      }
      for(at <- calleeMethodType.getArgumentTypes) {
        val opc         = at.toASMType.getOpcode(Opcodes.ISTORE)
        argStores.insert(new VarInsnNode(opc, nxtLocalIdx))
        nxtLocalIdx    += at.getSize
      }
      body.insert(argStores)

      // body's last instruction is a LabelNode denoting the single-exit point
      val postCall   = new asm.Label
      val postCallLN = new asm.tree.LabelNode(postCall)
      postCall.info  = postCallLN
      body.add(postCallLN)

          /**
           * body may contain xRETURN instructions, each should be replaced at that program point
           * by DROPs (as needed) for all slots but stack-top.
           */
          def replaceRETURNs() {
            val retType        = calleeMethodType.getReturnType
            val hasReturnValue = !retType.isUnitType
            val retVarIdx      = nxtLocalIdx
            nxtLocalIdx       += retType.getSize

            if(hasReturnValue) {
              val retVarLoad = {
                val opc = retType.toASMType.getOpcode(Opcodes.ILOAD)
                new VarInsnNode(opc, retVarIdx)
              }
              assert(body.getLast == postCallLN)
              body.insert(body.getLast, retVarLoad)
            }

                def retVarStore(retInsn: InsnNode) = {
                  val opc = retInsn.getOpcode match {
                    case Opcodes.IRETURN => Opcodes.ISTORE
                    case Opcodes.LRETURN => Opcodes.LSTORE
                    case Opcodes.FRETURN => Opcodes.FSTORE
                    case Opcodes.DRETURN => Opcodes.DSTORE
                    case Opcodes.ARETURN => Opcodes.ASTORE
                  }
                  new VarInsnNode(opc, retVarIdx)
                }

            val ca = new Analyzer[BasicValue](new BasicInterpreter)
            ca.analyze(callsite.owner, callee)
            val insnArr = callee.instructions.toArray // iterate this array while mutating callee.instructions at will
            for(calleeInsn <- insnArr;
                if calleeInsn.getOpcode >= Opcodes.IRETURN && calleeInsn.getOpcode <= Opcodes.RETURN)
            {
              val retInsn = calleeInsn.asInstanceOf[InsnNode]
              val frame   = ca.frameAt(retInsn)
              val height  = frame.getStackSize
              val counterpart = insnMap.get(retInsn)
              assert(counterpart.getOpcode == retInsn.getOpcode)
              assert(hasReturnValue == (retInsn.getOpcode != Opcodes.RETURN))
              val retRepl = new InsnList
              // deal with stack-top: either drop it or keep its value in retVar
              if(hasReturnValue)  { retRepl.add(retVarStore(retInsn)) }
              else if(height > 0) { retRepl.add(Util.getDrop(frame.peekDown(0).getSize)) }
              // deal with the rest of the stack
              for(slot <- 1 until height) {
                retRepl.add(Util.getDrop(frame.peekDown(slot).getSize))
              }
              retRepl.add(new JumpInsnNode(Opcodes.GOTO, postCallLN))
              body.insert(counterpart, retRepl)
              body.remove(counterpart)
            }
          }

      replaceRETURNs()

      host.instructions.insert(callsite, body) // after this point, body.isEmpty (an ASM instruction can be owned by a single InsnList)
      host.instructions.remove(callsite)

      // let the host know about the debug info of the callee
      host.localVariables.addAll(Util.cloneLocalVariableNodes(callee, labelMap, callee.name + "_"))
      host.tryCatchBlocks.addAll(Util.cloneTryCatchBlockNodes(callee, labelMap))

      // the host's local-var space grows by the local-var space of the callee, plus another local-var in case hasReturnValue
      Util.computeMaxLocalsMaxStack(host)
      assert(host.maxLocals >= nxtLocalIdx) // TODO why not == ?

      true

    } // end of method inlineMethod()

    /**
     * The second situation (a.2) under which method-inlining is unfeasible:
     *   In case access control doesn't give green light.
     *   Otherwise a java.lang.IllegalAccessError would be thrown at runtime.
     *
     * Quoting from the JVMS (our terminology: `there` stands for `C`; `here` for `D`):
     *
     *  5.4.4 Access Control
     *
     *  A class or interface C is accessible to a class or interface D if and only if either of the following conditions is true:
     *    (cond A1) C is public.
     *    (cond A2) C and D are members of the same runtime package (Sec 5.3).
     *
     *  A field or method R is accessible to a class or interface D if and only if any of the following conditions are true:
     *    (cond B1) R is public.
     *    (cond B2) R is protected and is declared in a class C, and D is either a subclass of C or C itself.
     *              Furthermore, if R is not static, then the symbolic reference to R
     *              must contain a symbolic reference to a class T, such that T is either a subclass
     *              of D, a superclass of D or D itself.
     *    (cond B3) R is either protected or has default access (that is, neither public nor
     *              protected nor private), and is declared by a class in the same runtime package as D.
     *    (cond B4) R is private and is declared in D.
     *
     *  This discussion of access control omits a related restriction on the target of a
     *  protected field access or method invocation (the target must be of class D or a
     *  subtype of D). That requirement is checked as part of the verification process
     *  (Sec 5.4.1); it is not part of link-time access control.
     *
     *  @param body
     *              instructions that will be inlined in a method in class `here`
     *  @param here
     *              class from which accesses given by `body` will take place.
     *
     */
    private def allAccessesLegal(body: InsnList, here: BType): Boolean = {

          def isAccessible(there: BType): Boolean = {
            if(!there.isNonSpecial) true
            else if (there.isArray) isAccessible(there.getElementType)
            else {
              assert(there.hasObjectSort, "not of object sort: " + there.getDescriptor)
              (there.getRuntimePackage == here.getRuntimePackage) || exemplars.get(there).isPublic
            }
          }

          /**
           * @return whether the first argument is a subtype of the second, or both are the same BType.
           */
          def isSubtypeOrSame(a: BType, b: BType): Boolean = {
            (a == b) || {
              val ax = exemplars.get(a)
              val bx = exemplars.get(b)

              (ax != null) && (bx != null) && ax.isSubtypeOf(b)
            }
          }

          /**
           * Furthermore, if R is not static, then the symbolic reference to R
           * must contain a symbolic reference to a class T, such that T is either a subclass
           * of D, a superclass of D or D itself.
           */
          def sameLineage(thereSymRef: BType): Boolean = {
            (thereSymRef == here) ||
            isSubtypeOrSame(thereSymRef, here) ||
            isSubtypeOrSame(here, thereSymRef)
          }

          def samePackageAsHere(there: BType): Boolean = { there.getRuntimePackage == here.getRuntimePackage }

          def memberAccess(flags: Int, thereOwner: BType, thereSymRef: BType) = {
            val key = { (Opcodes.ACC_PUBLIC | Opcodes.ACC_PROTECTED | Opcodes.ACC_PRIVATE) & flags }
            key match {

              case 0 /* default access */ => // (cond B3)
                samePackageAsHere(thereOwner)

              case Opcodes.ACC_PUBLIC     => // (cond B1)
                true

              case Opcodes.ACC_PROTECTED  =>
                // (cond B2)
                val condB2 = isSubtypeOrSame(here, thereOwner) && {
                  val isStatic = ((Opcodes.ACC_STATIC & flags) != 0)
                  isStatic || sameLineage(thereSymRef)
                }
                condB2 || samePackageAsHere(thereOwner)

              case Opcodes.ACC_PRIVATE    => // (cond B4)
                (thereOwner == here)
            }
          }

      val iter = body.iterator()
      while(iter.hasNext) {
        val insn    = iter.next()
        val isLegal = insn match {

          case ti: TypeInsnNode  => isAccessible(lookupRefBType(ti.desc))

          case fi: FieldInsnNode =>
            val fowner: BType = lookupRefBType(fi.owner)
            val fn: FieldNode = codeRepo.getFieldOrNull(fowner, fi.name, fi.desc)
            (fn != null) && memberAccess(fn.access, fowner, fowner)

          case mi: MethodInsnNode =>
            val thereSymRef: BType  = lookupRefBType(mi.owner)
            val mnAndOwner = codeRepo.getMethodOrNull(thereSymRef, mi.name, mi.desc) // TODO look up in superclasses too
            (mnAndOwner != null) && {
              val MethodNodeAndOwner(mn, thereClassNode) = mnAndOwner
              val thereOwner = lookupRefBType(thereClassNode.name)
              memberAccess(mn.access, thereOwner, thereSymRef)
            }

          case ivd: InvokeDynamicInsnNode => false // TODO

          case ci: LdcInsnNode =>
            ci.cst match {
              case t: asm.Type => isAccessible(lookupRefBType(t.getInternalName))
              case _           => true
            }

          case ma: MultiANewArrayInsnNode =>
            val et = descrToBType(ma.desc).getElementType
            if(et.hasObjectSort) isAccessible(et)
            else true

          case _ => true
        }
        if(!isLegal) {
          return false
        }
      }

      true
    } // end of method allAccessesLegal()

  } // end of class WholeProgramAnalysis

  /**
   * @param mnode a MethodNode, usually found via codeRepo.getMethod(bt: BType, name: String, desc: String)
   * @param owner ClassNode declaring mnode
   */
  case class MethodNodeAndOwner(mnode: MethodNode, owner: ClassNode) {
    assert(owner.methods.contains(mnode))
  }

} // end of class BCodeOpt