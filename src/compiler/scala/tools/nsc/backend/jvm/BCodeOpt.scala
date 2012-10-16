/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.tree.MethodNode


/**
 *  Optimize and tidy-up bytecode before it's emitted for good.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 *  TODO ConstantFolding, including specializing IFEQ etc
 *  TODO FieldValuePropagation, to propagate field accesses
 *
 *  TODO Improving the Precision and Correctness of Exception Analysis in Soot, http://www.sable.mcgill.ca/publications/techreports/#report2003-3
 */
abstract class BCodeOpt extends BCodeTypes {

  class BCodeCleanser(cnode: asm.tree.ClassNode) {

    val jumpsCollapser      = new asm.optimiz.JumpChainsCollapser(null)
    val unreachCodeRemover  = new asm.optimiz.UnreachableCode
    val labelsCleanup       = new asm.optimiz.LabelsCleanup(null)
    val danglingExcHandlers = new asm.optimiz.DanglingExcHandlers(null)

    val cpInterpreter       = new asm.optimiz.CopyInterpreter
    val copyPropagator      = new asm.optimiz.CopyPropagator
    val deadStoreElim       = new asm.optimiz.DeadStoreElim
    val ppCollapser         = new asm.optimiz.PushPopCollapser
    val unboxElider         = new UnBoxElider
    val jumpReducer         = new asm.optimiz.JumpReducer(null)
    val nullnessPropagator  = new asm.optimiz.NullnessPropagator

    val lvCompacter         = new asm.optimiz.LocalVarCompact(null)

    cleanseClass();

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

          } while(keepGoing)

          nullnessPropagator.transform(cName, mnode);   // infers null resp. non-null reaching certain program points, simplifying control-flow based on that.
          // keepGoing |= nullnessPropagator.changed

          lvCompacter.transform(mnode) // compact local vars, remove dangling LocalVariableNodes.
          runTypeFlowAnalysis(cName, mnode) // debug
        }
      }
    }

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

        unboxElider.transform(cName, mnode)    // remove unbox ops
        keepGoing |= unboxElider.changed

        jumpReducer.transform(mnode)           // simplifies branches that need not be taken to get to their destination.
        keepGoing |= jumpReducer.changed

        changed = (changed || keepGoing)

      } while (keepGoing)

      changed
    }

    def runTypeFlowAnalysis(owner: String, mnode: MethodNode) {

      import asm.tree.analysis.{ Analyzer, Frame }
      import asm.tree.AbstractInsnNode

      val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
      tfa.analyze(owner, mnode)
      val frames: Array[Frame[TFValue]]   = tfa.getFrames()
      val insns:  Array[AbstractInsnNode] = mnode.instructions.toArray()
      var i = 0
      while(i < frames.length) {
        if (frames(i) == null && insns(i) != null) {
          // TODO assert(false, "There should be no unreachable code left by now.")
        }
        i += 1
      }
    }

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

  }

  /**
   * Upon visiting an unbox callsite, copy-propagation may inform that some local-var holds
   * at that program-point the unboxed counterpart for the boxed value on top of the stack.
   * In this case, the unbox is replaced with two instructions (drop followed by load of the local).
   *
   * The code pattern above is common given that ... GenBCode emits it on purpose!
   * TODO it's counterproductive for a previous transform (e.g. peephole) to remove the {STORE_LOCAL; LOAD_LOCAL} sequence.
   *
   * Another transformer (PushPopCollapser) can be used to further simplify the resulting code,
   * which looks as follows after this transformation:
   *
   *     <load of unboxed value>
   *     STORE_LOCAL local-var
   *     LOAD_LOCAL  local-var
   *     BOX
   *     . . .
   *     // there used to be an UNBOX that was elided
   *     DROP
   *     LOAD_LOCAL local-var
   *
   * How to detect the code pattern to perform the rewriting?
   * Let's play out at the *microscopic* level how CopyPropagator interprets each instruction:
   *
   *     <load of unboxed value>    ---->    a SourceValue pointing to this instruction is pushed onto the stack
   *     STORE_LOCAL local-var      ---->    the above SourceValue is copied as-is to the slot for the local-var in question
   *     LOAD_LOCAL  local-var      ---->    the above SourceValue is pushed as-is onto the stack
   *     BOX                        ---->    pop of previous value, a new SourceValue is pushed.
   *                                         Its single producer is the same SourceValue (in the object identity sense)
   *                                         as for the local-var slot (provided the local-var couldn't have been overwritten in the meantime).
   *     UNBOX                      ---->    This is where the SourceValue described above is recognized.
   *
   *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
   *  @version 1.0
   *
   */
  class UnBoxElider {

    val BoxesRunTime = "scala/runtime/BoxesRunTime"

    import asm.tree.MethodInsnNode

    /** after transform() has run, this field records whether
     *  at least one pass of this transformer modified something. */
    var changed = false

    def transform(owner: String, mnode: MethodNode) {

      import asm.optimiz.{ProdConsAnalyzer, SSLUtil}

      changed = false;

      // compute the produce-consume relation (ie values flow from "producer" instructions to "consumer" instructions).
      val cp = new ProdConsAnalyzer(new CopyPCInterpreter)
      cp.analyze(owner, mnode);

      val frames = cp.getFrames()
      val insns  = mnode.instructions.toArray()

      var i = 0;
      while(i < frames.length) {
        if (frames(i) != null && insns(i) != null && SSLUtil.isScalaUnBox(insns(i))) {
          val unboxSV = frames(i).getStackTop
          // UNBOX must find something on the stack, yet it may happen that `unboxSV.insns.size() == 0`
          // because of the way Analyzer populates params-slots on method entry: they lack "producer" instructions.
          if(unboxSV.insns.size() == 1) {
            val unboxProd = unboxSV.insns.iterator().next();
            if(SSLUtil.isScalaBox(unboxProd)) {
              val boxIdx    = mnode.instructions.indexOf(unboxProd)
              val unboxedSV = frames(boxIdx).getStackTop
              var localIdx  = 0
              var keepGoing = (unboxedSV.insns.size() == 1)
              while(keepGoing && localIdx < mnode.maxLocals) {
                if(frames(i).getLocal(localIdx) eq unboxedSV) {
                  val drop      = new asm.tree.InsnNode(asm.Opcodes.POP)
                  val unboxedT  = asm.Type.getReturnType(insns(i).asInstanceOf[MethodInsnNode].desc)
                  val loadOpc   = unboxedT.getOpcode(asm.Opcodes.ILOAD)
                  val loadLocal = new asm.tree.VarInsnNode(loadOpc, localIdx)
                  mnode.instructions.insert(insns(i), drop)
                  mnode.instructions.insert(drop, loadLocal)
                  mnode.instructions.remove(insns(i))
                  changed   = true
                  keepGoing = false
                }
                localIdx += 1
              }
            }
            // TODO unpatch GenBCode (add unbox-var only when settings.optimise.value, currently always added)
          }
        }
        i += 1;
      }

    }

  }

  class CopyPCInterpreter extends asm.optimiz.ProdConsInterpreter {

    import asm.tree.AbstractInsnNode
    import asm.tree.analysis.SourceValue

    override def copyOperation(insn: AbstractInsnNode, value: SourceValue): SourceValue = {
      update(value, insn);
      return value;
    }

  }

}