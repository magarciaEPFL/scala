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
 *    (2) is of reference type;
 *  all while avoiding SI-5313.
 *
 *  In particular, every effort is made to eliminate dead-stores of THIS, not so much to eliminate the dead-store per-se,
 *  but to eliminate the usage of THIS, to unblock other transformations.
 *  For example, whenever the THIS of an anon-closure escapes the innermost apply, the anon-closure can't be inlined.
 *  Similarly, in order to "turn into static" an instance-method that actually doesn't depend on THIS.
 *  This last transformation in turn is useful when the method to statify is a dclosure-endpoint.
 *
 * Rewritings performed:
 *   (a) reassignment from same ===> drop instead of store
 *
 *   (b) assign RHS produced-by-ACONST_NULL to uninitialized LHS that goes unread ===> drop instead of store
 *       (assign null to null already simplified by NullnessPropagator)
 *
 *   (c) focus on ASTORE X for X != 0 in instanceMethod, where X goes unread, where RHS is FakeParamLoad(0)
 *       Note: FakeParamLoad(0) and not ALOAD_0, the latter could give us sthg other than FakeParamLoad(0)
 *       Subcases:
 *       (c.1) LHS slot contains uninit            ===> drop instead of store
 *       (c.2) LHS slot contains FakeParamLoad(0)  ===> drop instead of store -- covered by reassignment from same
 *       (c.3) LHS slot contains only ACONST_NULL instructions as producers ===> drop instead of store
 *       (c.4) LHS slot contains some other        ===> drop; ACONST_NULL; store
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class DeadStoreElimRef {

    public boolean changed = false;

    private UnBoxAnalyzer propag = null;
    private ProdConsAnalyzer cp  = null;

    public void transform(final String owner, final MethodNode mnode) throws AnalyzerException {

        changed = false;

        final boolean isInstanceMethod = Util.isInstanceMethod(mnode);

        // compute the produce-consume relation (ie values flow from "producer" instructions to "consumer" instructions).
        propag = UnBoxAnalyzer.create();
        Frame<SourceValue>[] frames = propag.analyze(owner, mnode);

        // another produce-consume relation, this time without jumping over copying instructions.
        cp = ProdConsAnalyzer.create();
        cp.analyze(owner, mnode);

        AbstractInsnNode[]   insns  = mnode.instructions.toArray();

        for(int i = 0; i < insns.length; i++) {
            AbstractInsnNode current = insns[i];
            if (current != null && Util.isSTORE(current)) {

                VarInsnNode        store = (VarInsnNode)current;
                Frame<SourceValue> f  = frames[i];

                final boolean isRefStoreToNonThis = (
                    (store.getOpcode() == Opcodes.ASTORE) && (!isInstanceMethod || (store.var != 0))
                );

                if (f.getStackTop() == f.getLocal(store.var)) {
                    // (a) reassignment from same ===> drop instead of store
                    dropInsteadOfStore(mnode, f, store);
                    changed = true;
                } else if (isRefStoreToNonThis && lacksConsumers(store) && isNULL(f.getStackTop()) && isUninit(f.getLocal(store.var))) {
                    // (b) assignment of NULL to uninitialized LHS that goes unread ===> drop instead of store
                    dropInsteadOfStore(mnode, f, store);
                    changed = true;
                } else if (isRefStoreToNonThis && lacksConsumers(store) && isTHIS(f.getStackTop())) {
                    // (c) focus on ASTORE X for X != 0 in instanceMethod, where X goes unread, where RHS is FakeParamLoad(0)
                    final SourceValue lhs = f.getLocal(store.var);
                    if ( isUninit(lhs) || isNULL(lhs)) {
                        // (c.1) LHS slot contains uninit            ===> drop instead of store
                        // (c.3) LHS slot contains only ACONST_NULL instructions as producers ===> drop instead of store
                        dropInsteadOfStore(mnode, f, store);
                        changed = true;
                    } else {
                        // (c.4) LHS slot contains some other        ===> drop; ACONST_NULL; store
                        mnode.instructions.insertBefore(store, Util.getDrop(1));
                        mnode.instructions.insertBefore(store, new InsnNode(Opcodes.ACONST_NULL));
                        changed = true;
                    }
                }

            }
        }

        propag = null;
        cp     = null;

    }

    /**
     *  Replaces the STORE given by `vi` with a DROP that consumes stack top.
     */
    private void dropInsteadOfStore(final MethodNode mnode, final Frame<SourceValue> f, final VarInsnNode vi) {
        int size = f.getStackTop().getSize();
        mnode.instructions.set(vi, Util.getDrop(size));
    }

    /**
     *  Whether the producers of `sv` are all of the form `ACONST_NULL` (with at least one producer).
     */
    private boolean isNULL(final SourceValue sv) {
        assert !(sv.insns.isEmpty());
        for (AbstractInsnNode prod : sv.insns) {
            if (prod instanceof UnBoxAnalyzer.FakeInsn) {
                return false;
            }
            if (prod.getOpcode() != Opcodes.ACONST_NULL) {
                return false;
            }
        }
        return true;
    }

    private boolean lacksConsumers(final AbstractInsnNode insn) {
        return cp.consumers(insn).isEmpty();
    }

    private boolean isTHIS(final SourceValue sv) {
        assert !(sv.insns.isEmpty());
        for (AbstractInsnNode prod : sv.insns) {
            if (!(prod instanceof UnBoxAnalyzer.FakeParamLoad)) {
                return false;
            }
            final UnBoxAnalyzer.FakeParamLoad fp = (UnBoxAnalyzer.FakeParamLoad) prod;
            if (!fp.isThisRef()) {
                return false;
            }
        }
        return true;
    }

    private boolean isUninit(final SourceValue sv) {
        assert !(sv.insns.isEmpty());
        for (AbstractInsnNode prod : sv.insns) {
            if (!(prod instanceof UnBoxAnalyzer.Uninitialized)) {
                return false;
            }
        }
        return true;
    }

}

