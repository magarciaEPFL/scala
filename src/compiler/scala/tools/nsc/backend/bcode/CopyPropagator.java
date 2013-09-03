/* NSC -- new Scala compiler
 * Copyright 2005-2013 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.nsc.backend.bcode;

import scala.tools.asm.Opcodes;

import scala.tools.asm.tree.AbstractInsnNode;
import scala.tools.asm.tree.MethodNode;
import scala.tools.asm.tree.VarInsnNode;

import scala.tools.asm.tree.analysis.AnalyzerException;
import scala.tools.asm.tree.analysis.Analyzer;
import scala.tools.asm.tree.analysis.Frame;
import scala.tools.asm.tree.analysis.SourceValue;
import scala.tools.asm.tree.analysis.SourceInterpreter;

/**
 *  Replaces the last link in a chain of data accesses (involving local-variables only)
 *  by a direct access to the chain-start.
 *
 *  A "chain of data accesses" refers to a assignments of the form shown below,
 *  without any intervening assignment to v, v1, v2, ..., v9:
 *
 *      v1 =  v
 *       ...
 *      v2 = v1
 *       ...
 *      v9 = v8
 *
 *  After CopyPropagator.transform() has run, `LOAD v9` has been replaced with `LOAD v`.
 *  Similarly for `LOAD v1` to `LOAD v8` (assuming the transformer is run until a fixpoint is reached).
 *
 *  Other than that, this method changes nothing else: in particular, say,
 *  `STORE v1` to `STORE v9` are left as-is.
 *
 *  To eliminate dead-stores, use `DeadStoreElim`.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 */
public class CopyPropagator {

    /** after transform() has run, this field records whether
     *  at least one pass of this transformer modified something. */
    private boolean changed = false;

    public boolean changed() { return changed; }

    public void transform(final String owner, final MethodNode mnode) throws AnalyzerException {

        DisambiguatingAnalyzer propag = DisambiguatingAnalyzer.create();
        propag.analyze(owner, mnode);

        Frame<SourceValue>[] frames = propag.getFrames();
        AbstractInsnNode[]   insns  = mnode.instructions.toArray();

        changed = false;

        int i = 0;
        while (i < insns.length) {
            boolean isVarInsn = (
              insns[i] != null &&
              insns[i].getType()   == AbstractInsnNode.VAR_INSN &&
              insns[i].getOpcode() != Opcodes.RET
            );
            if (isVarInsn) {
              VarInsnNode vnode  = (VarInsnNode)insns[i];
              Frame<SourceValue> frame  = frames[i];
              boolean isLoad = (vnode.getOpcode() >= Opcodes.ILOAD && vnode.getOpcode() <= Opcodes.ALOAD);
              SourceValue source = (isLoad ? frame.getLocal(vnode.var) : frame.getStackTop());
              boolean hasUniqueSource = (source.insns.size() == 1);
              if (hasUniqueSource && isLoad) {
                int j = 0;
                while (j < vnode.var) {
                  if (frame.getLocal(j) == source) {
                    if (vnode.var != j) {
                        vnode.var = j;
                        changed = true;
                    }
                  }
                  j += 1;
                }
              }
            }
            i += 1;
        }

    }

    /**
     * Propagates the input value through LOAD, STORE, DUP, and SWAP instructions.
     */
    static private class SourceCopyInterpreter extends SourceInterpreter {

        @Override
        public SourceValue copyOperation(final AbstractInsnNode insn, final SourceValue value) {
            return value;
        }

    }

}
