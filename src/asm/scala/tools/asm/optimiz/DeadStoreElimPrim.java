/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import scala.tools.asm.Opcodes;
import scala.tools.asm.tree.*;

import scala.tools.asm.tree.analysis.*;

/**
 *
 *  This transformer elides operations on a local-var provided the local in question:
 *    (1) isn't used afterwards, and
 *    (2) is of primitive type.
 *
 *  Restriction (2) is a conservative way to avoid SI-5313. The description in ticket SI-5313
 *  highlights the case where a STORE that assigns NULL is kept
 *  (such STORE prompts the garbage collector to notify via a WeakReference).
 *  A similar argument can be made about a STORE with non-null RHS, in this case the desired behavior
 *  might well be to prevent the garbage collector from releasing the RHS value.
 *
 *  Three rewritings are performed:
 *
 *    (a) Replace (a STORE instruction for a local-var of primitive type which isn't live) with a DROP instruction.
 *        In particular, the initialization of (a local-var that is never read) is replaced with DROP.
 *        This rewriting doesn't lead to non-definitely-initialized errors, because the local-vars is never read anyway.
 *
 *    (b) Remove an IINC instruction for a non-live local.
 *
 *    (c) Elide a STORE-LOAD pair provided the local (of primitive type) isn't used afterwards.
 *        For example:
 *           9:  istore_2
 *          10:  iload_2  // no intervening LabelNode between previous instruction and this one
 *        ie there's no consumer for the STORE instruction above other than the (immediately following) LOAD.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class DeadStoreElimPrim {

    public boolean changed = false;

    private ProdConsAnalyzer cp = null;

    public void transform(final String owner, final MethodNode mnode) throws AnalyzerException {

        changed = false;

        // compute the produce-consume relation (ie values flow from "producer" instructions to "consumer" instructions).
        cp = ProdConsAnalyzer.create();
        Frame<SourceValue>[] frames = cp.analyze(owner, mnode);
        AbstractInsnNode[]   insns  = mnode.instructions.toArray();

        for(int i = 0; i < insns.length; i++) {
            AbstractInsnNode current = insns[i];
            if (current != null) {
                if (Util.isSTORE(current) && (current.getOpcode() != Opcodes.ASTORE)) {
                    // ruling out ASTORE, a conservative way to avoid SI-5313.
                    if (cp.consumers(current).isEmpty()) {
                        // Rewriting: elide STORE to a local that sees no use afterwards.
                        int size = frames[i].getStackTop().getSize();
                        mnode.instructions.set(current, Util.getDrop(size));
                        changed = true;
                    } else if (isRedundantStoreLoad((VarInsnNode)current)) {
                        // Rewriting: elide a STORE-LOAD pair provided the local isn't used afterwards.
                        mnode.instructions.remove(current.getNext());
                        mnode.instructions.remove(current);
                        i++;
                        changed = true;
                    }

                } else if (current.getOpcode() == Opcodes.IINC && cp.consumers(current).isEmpty()) {
                    // Rewriting: remove IINC of a local that sees no use afterwards.
                    // BTW, IINC doesn't show up in Scala-emitted code.
                    mnode.instructions.remove(current);
                    changed = true;
                }
            }
        }
    }

    private boolean isRedundantStoreLoad(VarInsnNode current) {
        assert Util.isSTORE(current);
        if (current.getOpcode() == Opcodes.ASTORE) {
            // ruling out ASTORE, a conservative way to avoid SI-5313.
            return false;
        }
        AbstractInsnNode nxt = Util.execInsnOrLabelAfter(current);
        if (nxt != null && Util.isLOAD(nxt)) {
            if (Util.denoteSameLocal(current, nxt) && cp.isPointToPoint(current, nxt)) {
                return true;
            }
        }
        return false;
    }

}
