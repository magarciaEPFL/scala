/* NSC -- new Scala compiler
 * Copyright 2005-2013 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc.backend.bcode;

import scala.tools.asm.*;
import scala.tools.asm.tree.*;

import scala.tools.asm.tree.analysis.AnalyzerException;

import java.util.*;

/**
 *  Some transformations (eg DeadStoreElim) mark computations as redundant by inserting DROP instructions to discard computed values.
 *
 *  This transformation starts from there by removing those (producer, consumer) pairs where
 *  the consumer is a DROP and the producer has its value consumed only by the DROP in question.
 *  (More general cases are possible, but the above covers the inlining scenario).
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class PushPopCollapser {

    private ProdConsAnalyzer cp = null;
    private MethodNode mnode = null;

    /** after transform() has run, this field records whether
     *  at least one pass of this transformer modified something. */
    private boolean changed = false;

    public boolean changed() { return changed; }

    public void transform(final String owner, final MethodNode mnode) throws AnalyzerException {

        this.mnode = mnode;

        changed = false;
        boolean keepGoing = false;

        final Set<AbstractInsnNode> skipExam = new HashSet<AbstractInsnNode>();

        do {

            keepGoing = false;

            // compute the produce-consume relation (ie values flow from "producer" instructions to "consumer" instructions).
            this.cp = ProdConsAnalyzer.create();
            this.cp.analyze(owner, mnode);

            final Iterator<AbstractInsnNode> iter = mnode.instructions.iterator();

            while (iter.hasNext()) {
                final AbstractInsnNode current = iter.next();
                if (current != null && Util.isDROP(current) && !skipExam.contains(current)) {
                    final InsnNode drop = (InsnNode) current;
                    final boolean isElidable = isSoleConsumerForItsProducers(drop);
                    if (isElidable) {
                        final Set<AbstractInsnNode> producers = cp.producers(drop);
                        int size = (drop.getOpcode() == Opcodes.POP ? 1 : 2);
                        boolean wasSimplified = (neutralizeStackPush(producers, size, skipExam) > 0);
                        if (wasSimplified) {
                            keepGoing = true;
                        }
                        mnode.instructions.remove(drop);
                    } else {
                        skipExam.add(drop);
                    }
                }
            }

            changed = (changed || keepGoing);

        } while (keepGoing);

    }

    private boolean isSoleConsumerForItsProducers(InsnNode drop) {
        final Set<AbstractInsnNode> ps = cp.producers(drop);
        if (ps.isEmpty()) {
            // POP as first instruction of an exception handler has no explicit producers.
            // A pseudo-instruction could be used to denote the implicit producer (see UnBoxAnalyzer.FakeEHLoad)
            // Instead, it's more expedient to just veto the eliding of that POP, by returning false.
            return false;
        }
        return cp.isMux(ps, drop);
    }

    private boolean isAlreadyMinimized(final Set<AbstractInsnNode> producers, InsnNode drop) {
        final int opc = drop.getOpcode();
        assert opc == Opcodes.POP || opc == Opcodes.POP2;
        if (producers.size() == 1) {
            AbstractInsnNode singleProd = producers.iterator().next();
            final int size = (opc - 86);
            if (singleProd.getNext() == drop && !canSimplify(singleProd, size)) {
                return true;
            }
        }
        return false;
    }

    /**
     *  All we know about the "producer" instructions is each of them pushes a value we don't need onto the stack,
     *  while we still need any side-effects producers might have.
     *
     *  A blanket way to "neutralize stack push" of a "producer" instruction involves:
     *    (a) leaving the producer in place, and
     *    (b) inserting a POP or POP2 right after it, based on the `size` argument.
     *
     *  That's what we do unless a special case is detected.
     *  For example, for IADD shorter code is emitted by replacing IADD with two POP instructions.
     *  Similarly for other producers.
     *  The added POP instructions may in turn be used to "neutralize" their producers, and so on.
     *
     *  TODO-1 elide a field-load followed by drop (for both instance and static fields) unless the field is volatile.
     *  PeepholeOpt does it like so:
     *   case (LOAD_FIELD(sym, isStatic), DROP(_)) if !sym.hasAnnotation(definitions.VolatileAttr) =>
     *     if (isStatic) Some(Nil)
     *     else          Some(DROP(REFERENCE(definitions.ObjectClass)) :: Nil)
     *
     */
    private int neutralizeStackPush(final Set<AbstractInsnNode> producers, final int size, final Set<AbstractInsnNode> skipExam) {
        assert !producers.isEmpty() : "There can't be a POP or POP2 without some other instruction pushing a value for it on the stack.";

        // accumulates how many producers were simplified (as part of which they are removed),
        // ie not counting leaving the producer in place and appending a DROP.
        int simplified = 0;

        final Iterator<AbstractInsnNode> iter = producers.iterator();
        while (iter.hasNext()) {

            final AbstractInsnNode prod = iter.next();
            final int opc = prod.getOpcode();

            switch (opc) {

                case Opcodes.ACONST_NULL:
                case Opcodes.ICONST_M1:
                case Opcodes.ICONST_0:
                case Opcodes.ICONST_1:
                case Opcodes.ICONST_2:
                case Opcodes.ICONST_3:
                case Opcodes.ICONST_4:
                case Opcodes.ICONST_5:
                case Opcodes.LCONST_0:
                case Opcodes.LCONST_1:
                case Opcodes.FCONST_0:
                case Opcodes.FCONST_1:
                case Opcodes.FCONST_2:
                case Opcodes.DCONST_0:
                case Opcodes.DCONST_1:
                case Opcodes.BIPUSH:
                case Opcodes.SIPUSH:
                case Opcodes.ILOAD:
                case Opcodes.LLOAD:
                case Opcodes.FLOAD:
                case Opcodes.DLOAD:
                case Opcodes.ALOAD:
                    removeProducer(prod);
                    break;

                case Opcodes.LDC:
                    LdcInsnNode ldc = (LdcInsnNode)prod;
                    boolean mayInitClass = (ldc.cst instanceof Type);
                    if (mayInitClass) {
                        /*
                         * Summary: LDC of a class-literal never cancels-out with a POP1 instruction.
                         * Before discussing why, some context: there's a VM-level behavioral difference across JDKs regarding class-literals.
                         *   (a) in Java 1.4 and earlier, a reference to Foo.class has the side-effect of
                         *       running the static initializer of Foo (unless it has executed already).
                         *   (b) in Java 5 and later, it does not.
                         *       Details at http://www.oracle.com/technetwork/java/javase/compatibility-137462.html
                         * In all cases, this optimization leaves in place the load of class-literal, even if it's about to be POP1.
                         * One more reason to leave the class literal in place involves NoClassDefFoundError at runtime
                         * (that we want to preserve, eliding the load of class literal might make that error go away).
                         */
                        skipExam.add(appendDrop(prod, 1));
                    } else {
                        removeProducer(prod);
                    }
                    break;

                case Opcodes.IALOAD:
                case Opcodes.LALOAD:
                case Opcodes.FALOAD:
                case Opcodes.DALOAD:
                case Opcodes.AALOAD:
                case Opcodes.BALOAD:
                case Opcodes.CALOAD:
                case Opcodes.SALOAD:
                    // none of these gets elided to prevent swallowing NPE, out of bounds, exceptions.
                    skipExam.add(appendDrop(prod, size));
                    break;

                case Opcodes.ISTORE:
                case Opcodes.LSTORE:
                case Opcodes.FSTORE:
                case Opcodes.DSTORE:
                case Opcodes.ASTORE:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.IASTORE:
                case Opcodes.LASTORE:
                case Opcodes.FASTORE:
                case Opcodes.DASTORE:
                case Opcodes.AASTORE:
                case Opcodes.BASTORE:
                case Opcodes.CASTORE:
                case Opcodes.SASTORE:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.POP:
                case Opcodes.POP2:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.DUP:
                    assert size == 1;
                    removeProducer(prod);
                    break;

                case Opcodes.DUP2:
                    if (size == 2) {
                        removeProducer(prod);
                    } else {
                        skipExam.add(appendDrop(prod, size));
                    }
                    break;

                case Opcodes.DUP_X1:
                case Opcodes.DUP_X2:
                case Opcodes.DUP2_X1:
                case Opcodes.DUP2_X2:
                case Opcodes.SWAP:
                    skipExam.add(appendDrop(prod, size));
                    break;

                case Opcodes.IDIV:
                case Opcodes.LDIV:
                case Opcodes.IREM:
                case Opcodes.LREM:
                    // Summing up the discussion in ConstantFolder about zero divisor and integer division, integer remainder.
                    // The possibility of zero divisor can't be ruled out by PushPopCollapser,
                    // thus IDIV followed by POP1 can't be simplified further. Similarly for LDIV and for IREM, LREM.
                    skipExam.add(appendDrop(prod, size));
                    break;

                case Opcodes.IADD:
                case Opcodes.LADD:
                case Opcodes.FADD:
                case Opcodes.DADD:
                case Opcodes.ISUB:
                case Opcodes.LSUB:
                case Opcodes.FSUB:
                case Opcodes.DSUB:
                case Opcodes.IMUL:
                case Opcodes.LMUL:
                case Opcodes.FMUL:
                case Opcodes.DMUL:
                case Opcodes.FDIV:
                case Opcodes.DDIV:
                case Opcodes.FREM:
                case Opcodes.DREM:
                    replaceProducer(size, size, prod);
                    break;

                case Opcodes.INEG:
                case Opcodes.LNEG:
                case Opcodes.FNEG:
                case Opcodes.DNEG:
                    replaceProducer(size, prod);
                    break;

                case Opcodes.ISHL:
                case Opcodes.ISHR:
                case Opcodes.IUSHR:
                    assert size == 1;
                    replaceProducer(1, 1, prod);
                    break;

                case Opcodes.LSHL:
                case Opcodes.LSHR:
                case Opcodes.LUSHR:
                    assert size == 2;
                    replaceProducer(2, 1, prod); // ie at runtime: POP followed by POP2.
                    break;

                case Opcodes.IAND:
                case Opcodes.IOR:
                case Opcodes.IXOR:
                    assert size == 1;
                    replaceProducer(1, 1, prod);
                    break;

                case Opcodes.LAND:
                case Opcodes.LOR:
                case Opcodes.LXOR:
                    assert size == 2;
                    replaceProducer(2, 2, prod);
                    break;

                case Opcodes.IINC:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.I2L:
                case Opcodes.I2F:
                case Opcodes.I2D:
                    replaceProducer(1, prod);
                    break;

                case Opcodes.L2I:
                case Opcodes.L2F:
                case Opcodes.L2D:
                    replaceProducer(2, prod);
                    break;

                case Opcodes.F2I:
                case Opcodes.F2L:
                case Opcodes.F2D:
                    replaceProducer(1, prod);
                    break;

                case Opcodes.D2I:
                case Opcodes.D2L:
                case Opcodes.D2F:
                    replaceProducer(2, prod);
                    break;

                case Opcodes.I2B:
                case Opcodes.I2C:
                case Opcodes.I2S:
                    replaceProducer(1, prod);
                    break;

                case Opcodes.LCMP:
                    replaceProducer(2, 2, prod);
                    break;

                case Opcodes.FCMPL:
                case Opcodes.FCMPG:
                    replaceProducer(1, 1, prod);
                    break;

                case Opcodes.DCMPL:
                case Opcodes.DCMPG:
                    replaceProducer(2, 2, prod);
                    break;

                case Opcodes.IFEQ:
                case Opcodes.IFNE:
                case Opcodes.IFLT:
                case Opcodes.IFGE:
                case Opcodes.IFGT:
                case Opcodes.IFLE:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.IF_ICMPEQ:
                case Opcodes.IF_ICMPNE:
                case Opcodes.IF_ICMPLT:
                case Opcodes.IF_ICMPGE:
                case Opcodes.IF_ICMPGT:
                case Opcodes.IF_ICMPLE:
                case Opcodes.IF_ACMPEQ:
                case Opcodes.IF_ACMPNE:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.GOTO:
                case Opcodes.JSR:
                case Opcodes.RET:
                case Opcodes.TABLESWITCH:
                case Opcodes.LOOKUPSWITCH:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.IRETURN:
                case Opcodes.LRETURN:
                case Opcodes.FRETURN:
                case Opcodes.DRETURN:
                case Opcodes.ARETURN:
                case Opcodes.RETURN:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.GETSTATIC:
                    if (SSLUtil.isSideEffectFreeGETSTATIC(prod)) {
                        removeProducer(prod);
                    } else {
                        assert size == SizingUtil.getResultSize(prod);
                        skipExam.add(appendDrop(prod, size));
                    }
                    break;

                case Opcodes.PUTSTATIC:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.GETFIELD:
                    assert size == SizingUtil.getResultSize(prod);
                    skipExam.add(appendDrop(prod, size));
                    break;

                case Opcodes.PUTFIELD:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.INVOKEVIRTUAL:
                case Opcodes.INVOKESPECIAL:
                case Opcodes.INVOKESTATIC:
                case Opcodes.INVOKEINTERFACE: {
                    if (SSLUtil.isSideEffectFreeCall(prod)) {

                        // replace the call-instruction that pushes with as many DROPs as arguments it expects on the stack.
                        MethodInsnNode mi = (MethodInsnNode) prod;
                        Type[] argTs = Type.getArgumentTypes(mi.desc);
                        for(int argIdx = 0; argIdx < argTs.length; argIdx++) {
                            mnode.instructions.insert(prod, Util.getDrop(argTs[argIdx].getSize()));
                        }
                        if (opc != Opcodes.INVOKESTATIC) {
                            mnode.instructions.insert(prod, Util.getDrop(1));
                        }
                        mnode.instructions.remove(prod);


                    } else {

                        assert size == SizingUtil.getResultSize(prod);
                        skipExam.add(appendDrop(prod, size));

                    }
                    break;
                }
                case Opcodes.INVOKEDYNAMIC:
                    skipExam.add(appendDrop(prod, size));
                    break;

                case Opcodes.NEW:
                    // TODO some instantiations are side-effect free, and could be elided.
                    assert size == 1;
                    skipExam.add(appendDrop(prod, size));
                    break;

                case Opcodes.NEWARRAY:
                case Opcodes.ANEWARRAY:
                    replaceProducer(1, prod);
                    break;

                case Opcodes.ARRAYLENGTH:
                    assert size == 1;
                    skipExam.add(appendDrop(prod, size));
                    break;

                case Opcodes.ATHROW:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.CHECKCAST:
                    assert size == 1;
                    skipExam.add(appendDrop(prod, size));
                    break;

                case Opcodes.INSTANCEOF:
                    // we might swallow at runtime a NoClassDefFoundError,
                    // but we've got a program that typechecks, right? So there should be no exception anyway.
                    replaceProducer(1, prod);
                    break;

                case Opcodes.MONITORENTER:
                case Opcodes.MONITOREXIT:
                    assert false : "not a stack-loading instruction";
                    break;

                case Opcodes.MULTIANEWARRAY:
                    for (int i = ((MultiANewArrayInsnNode) prod).dims; i > 0; --i) {
                        mnode.instructions.insert(prod, Util.getDrop(1));
                    }
                    mnode.instructions.remove(prod);
                    break;

                case Opcodes.IFNULL:
                case Opcodes.IFNONNULL:
                    assert false : "not a stack-loading instruction";
                    break;

                default:
                    throw new RuntimeException("Illegal opcode "+prod.getOpcode());

            }

            if (!mnode.instructions.contains(prod)) {
                simplified++;
            }

        }

        return simplified;
    }

    private void removeProducer(final AbstractInsnNode prod) {
        mnode.instructions.remove(prod);
    }

    private InsnNode appendDrop(final AbstractInsnNode prod, final int size) {
        InsnNode drop = Util.getDrop(size);
        mnode.instructions.insert(prod, drop);
        return drop;
    }

    private void replaceProducer(final int dropSize, final AbstractInsnNode prod) {
        mnode.instructions.set(prod, Util.getDrop(dropSize));
    }

    /**
     *  This method assumes `prod` expects an operand stack with the following shape:
     *
     *      ..., oneBelow, stackTop
     *
     *  ie `prod` would consume both elements and then push another (not shown).
     *
     *  This method "neutralizes" such stack push by removing `prod` from the instruction stream.
     *  In order to adjust the stack, two drop instructions are necessary:
     *    (1) for stack top,     whose size is given by THE SECOND argument to this method.
     *    (2) for one below top, whose size is given by THE FIRST  argument to this method.
     *
     */
    private void replaceProducer(final int oneBelowSize, final int stackTopSize, final AbstractInsnNode prod) {
        mnode.instructions.insert(prod, Util.getDrop(stackTopSize));
        mnode.instructions.insert(prod, Util.getDrop(oneBelowSize));
        mnode.instructions.remove(prod);
    }

    /**
     *  This has to be maintained in agreement with ConstantFolder.transform()
     *  The rule of thumb is: if that method just limits itself to placing a drop instruction right after the producer instruction,
     *  then that instruction "can't be simplified" any further.
     */
    private boolean canSimplify(final AbstractInsnNode producer, final int size) {

        switch (producer.getOpcode()) {

            case Opcodes.IALOAD:
            case Opcodes.LALOAD:
            case Opcodes.FALOAD:
            case Opcodes.DALOAD:
            case Opcodes.AALOAD:
            case Opcodes.BALOAD:
            case Opcodes.CALOAD:
            case Opcodes.SALOAD:
                return false;

            case Opcodes.DUP2:
                return (size == 2);

            case Opcodes.DUP_X1:
            case Opcodes.DUP_X2:
            case Opcodes.DUP2_X1:
            case Opcodes.DUP2_X2:
            case Opcodes.SWAP:
                return false;

            case Opcodes.IDIV:
            case Opcodes.LDIV:
            case Opcodes.IREM:
            case Opcodes.LREM:
                // Summing up the discussion in ConstantFolder about zero divisor and integer division, integer remainder.
                // The possibility of zero divisor can't be ruled out by PushPopCollapser,
                // thus IDIV followed by POP1 can't be simplified further. Similarly for LDIV and for IREM, LREM.
                return false;

            case Opcodes.GETSTATIC:
                return SSLUtil.isSideEffectFreeGETSTATIC(producer);

            case Opcodes.GETFIELD:
                return false;

            case Opcodes.INVOKEVIRTUAL:
            case Opcodes.INVOKESPECIAL:
            case Opcodes.INVOKESTATIC:
            case Opcodes.INVOKEINTERFACE:
                return SSLUtil.isSideEffectFreeCall(producer);

            case Opcodes.INVOKEDYNAMIC:
            case Opcodes.NEW:
            case Opcodes.ARRAYLENGTH:
            case Opcodes.CHECKCAST:
                return false;

            case Opcodes.LDC:
                LdcInsnNode ldc = (LdcInsnNode)producer;
                boolean mayInitClass = (ldc.cst instanceof Type);
                return !mayInitClass;

            default:
                return true;

        }

    }

}

