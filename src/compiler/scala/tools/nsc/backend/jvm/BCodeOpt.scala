/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm

import asm.optimiz.{LocalVarCompact, CopyInterpreter}
import asm.tree.analysis.SourceValue
import asm.tree.{VarInsnNode, MethodNode}

/**
 *  Optimize and tidy-up bytecode before it's emitted for good.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOpt extends BCodeTypes {

  class BCodeCleanser(cnode: asm.tree.ClassNode) {

    val jumpsCollapser      = new asm.optimiz.JumpChainsCollapser(null)
    val labelsCleanup       = new asm.optimiz.LabelsCleanup(null)
    val danglingExcHandlers = new asm.optimiz.DanglingExcHandlers(null)
    val lvCompacter         = new asm.optimiz.LocalVarCompact(null)

    val cpInterpreter       = new asm.optimiz.CopyInterpreter

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
          cleanseMethod(cName, mnode)
          copyPropagate(cName, mnode)
          runTypeFlowAnalysis(cName, mnode)
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
     *  TODO PENDING (assuming their activation conditions will trigger):
     *    - peephole rewriting
     *    - Improving the Precision and Correctness of Exception Analysis in Soot, http://www.sable.mcgill.ca/publications/techreports/#report2003-3
     *
     */
    def cleanseMethod(cName: String, mnode: asm.tree.MethodNode) {
      jumpsCollapser.transform(mnode)           // collapse a multi-jump chain to target its final destination via a single jump
      repOK(mnode)
      removeUnreachableCode(cName, mnode)       // remove unreachable code
      repOK(mnode)

      do {
        jumpsCollapser.transform(mnode)
        repOK(mnode)

        removeUnreachableCode(cName, mnode)
        repOK(mnode)

        labelsCleanup.transform(mnode)          // remove those LabelNodes and LineNumbers that aren't in use
        repOK(mnode)

        danglingExcHandlers.transform(mnode)
        repOK(mnode)

        if(danglingExcHandlers.changed) {
          removeUnreachableCode(cName, mnode)
          labelsCleanup.transform(mnode)
        }
      } while (danglingExcHandlers.changed)

      lvCompacter.transform(mnode)

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
     *  Replaces the last link in a chain of data accesses by a direct access to the chain-start.
     *  A "chain of data accesses" refers to a assignments of the form shown below,
     *  without any intervening rewriting of v, v1, v2, ..., v9:
     *
     *      v1 =  v
     *       ...
     *      v2 = v1
     *       ...
     *      v9 = v8
     *
     *  After this method has run, `LOAD v9` has been replaced with `LOAD v`
     *
     */
    def copyPropagate(owner: String, mnode: MethodNode) {

      import asm.tree.analysis.{ Analyzer, Frame }
      import asm.tree.AbstractInsnNode

      val propag = new Analyzer[SourceValue](new CopyInterpreter)
      propag.analyze(owner, mnode)
      val frames: Array[Frame[SourceValue]] = propag.getFrames()
      val insns:  Array[AbstractInsnNode]   = mnode.instructions.toArray()
      var i = 0
      while(i < frames.length) {
        val isVarInsn = {
          insns(i) != null &&
          insns(i).getType   == AbstractInsnNode.VAR_INSN &&
          insns(i).getOpcode != asm.Opcodes.RET
        }
        if (isVarInsn) {
          val vnode  = insns(i).asInstanceOf[VarInsnNode]
          val frame  = frames(i)
          val isLoad = (vnode.getOpcode >= asm.Opcodes.ILOAD && vnode.getOpcode <= asm.Opcodes.ALOAD)
          val source =
            if(isLoad) { frame.getLocal(vnode.`var`) }
            else       { frame.getStack(frame.getStackSize - 1) }
          val hasUniqueSource = (source.insns.size() == 1)
          if(hasUniqueSource && isLoad) {
            var j = 0
            while(j < vnode.`var`) {
              if(frame.getLocal(j) eq source) {
                vnode.`var` = j
              }
              j += 1
            }
          }
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

    /**
     * Detects and removes unreachable code.
     *
     * Should be used last in a transformation chain, before stack map frames are computed.
     * The Java 6 verifier demands frames be available even for dead code.
     * Those frames are tricky to compute, http://asm.ow2.org/doc/developer-guide.html#deadcode
     * The problem is avoided altogether by not emitting unreachable code in the first place.
     *
     */
    def removeUnreachableCode(owner: String, mnode: MethodNode) {

      import asm.tree.analysis.{ Analyzer, AnalyzerException, BasicInterpreter, BasicValue, Frame }
      import asm.tree.{ AbstractInsnNode, LabelNode }

      val a = new Analyzer[BasicValue](new BasicInterpreter)
      try {
        a.analyze(owner, mnode)
        val frames: Array[Frame[BasicValue]] = a.getFrames()
        val insns:  Array[AbstractInsnNode]  = mnode.instructions.toArray()
        var i = 0
        while(i < frames.length) {
          if (frames(i) == null &&
              insns(i)  != null &&
              !(insns(i).isInstanceOf[LabelNode])) {
            mnode.instructions.remove(insns(i));
          }
          i += 1
        }
      } catch {
        case ignored : AnalyzerException  => ()
      }
    }

  }

}