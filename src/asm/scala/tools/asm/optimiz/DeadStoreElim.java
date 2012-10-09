/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import scala.tools.asm.Opcodes;
import scala.tools.asm.tree.*;

import scala.tools.asm.tree.analysis.AnalyzerException;

/**
 *  Replaces STORE instructions for local-vars which aren't live with DROP instructions.
 *  A local-var is deemed live iff some instruction other than DROP consumes its value.
 *
 *  In particular, the initialization of a loca-var that is never read is replaced with DROP.
 *
 *  The rewriting performed here doesn't lead to non-definitely-initialized errors,
 *  because the local-vars in question are never read.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class DeadStoreElim {

    public boolean changed = false;

    public void transform(final String owner, final MethodNode mnode) throws AnalyzerException {

        changed = false;

        // find the instructions consuming values produced by other instructions.
        ProdConsAnalyzer cp = ProdConsAnalyzer.create();
        cp.analyze(owner, mnode);
        AbstractInsnNode[] insns  = mnode.instructions.toArray();

        for(int i = 0; i < insns.length; i++) {
            AbstractInsnNode current = insns[i];
            if (current != null  && Util.isSTORE(current) && !cp.hasConsumers(current)) {
                int size = cp.frameAt(current).getStackTop().getSize();
                mnode.instructions.set(current, Util.getDrop(size));
                changed = true;
            }
            if (current != null  && current.getOpcode() == Opcodes.IINC && !cp.hasConsumers(current)) {
                // IINC doesn't show up in Scala-emitted code.
                mnode.instructions.remove(current);
                changed = true;
            }
        }
    }

}
