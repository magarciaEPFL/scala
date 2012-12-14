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
 *  Optimize and tidy-up bytecode before it's serialized for good.
 *  This class focuses on intra-method optimizations and optimization infrastructure.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 *  TODO Improving the Precision and Correctness of Exception Analysis in Soot, http://www.sable.mcgill.ca/publications/techreports/#report2003-3
 *
 */
abstract class BCodeOptIntra extends BCodeTypes {

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
    val unusedPrivateElider = new asm.optimiz.UnusedPrivateElider()

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

          basicIntraMethodOpt(cName, mnode)

          cacheRepeatableReads(cName, mnode)

          unboxElider.transform(cName, mnode)   // remove box/unbox pairs (this transformer is more expensive than most)
          lvCompacter.transform(mnode)          // compact local vars, remove dangling LocalVariableNodes.

          // val before = text(cnode.innerClasses)
          refreshInnerClasses(cnode)
          // val after  = text(cnode.innerClasses)

          runTypeFlowAnalysis(cName, mnode) // debug
        }
      }

      val cnodeEx = exemplars.get(lookupRefBType(cnode.name))
      if(!settings.keepUnusedPrivateClassMembers.value && !cnodeEx.isSubtypeOf(jioSerializableReference)) {
        unusedPrivateElider.transform(cnode)
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

    def basicIntraMethodOpt(cName: String, mnode: asm.tree.MethodNode) {
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

} // end of class BCodeOptIntra