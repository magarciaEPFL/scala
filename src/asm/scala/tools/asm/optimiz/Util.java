/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import scala.tools.asm.Opcodes;
import scala.tools.asm.Type;
import scala.tools.asm.tree.AbstractInsnNode;
import scala.tools.asm.tree.InsnNode;
import scala.tools.asm.tree.LdcInsnNode;
import scala.tools.asm.tree.LabelNode;

/**
 *  Utilities.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class Util {

    // ------------------------------------------------------------------------
    // utilities to classify instructions
    // ------------------------------------------------------------------------

    public static boolean isLOAD(final AbstractInsnNode insn) {
        final int opc = insn.getOpcode();
        return (opc >= Opcodes.ILOAD  && opc <= Opcodes.ALOAD);
    }

    public static boolean isPrimitiveConstant(final AbstractInsnNode insn) {
        final int opc = insn.getOpcode();
        boolean result = (opc >= Opcodes.ACONST_NULL && opc <= Opcodes.SIPUSH);
        result |= (opc == Opcodes.LDC && !isStringConstant(insn) && !isTypeConstant(insn));
        return result;
    }

    public static boolean isStringConstant(final AbstractInsnNode insn) {
        if(insn.getOpcode() != Opcodes.LDC) {
             return false;
        }
        final LdcInsnNode ldc = (LdcInsnNode)insn;
        return (ldc.cst instanceof String);
    }

    public static boolean isTypeConstant(final AbstractInsnNode insn) {
        if(insn.getOpcode() != Opcodes.LDC) {
             return false;
        }
        final LdcInsnNode ldc = (LdcInsnNode)insn;
        return (ldc.cst instanceof Type);
    }

    public static boolean isSTORE(final AbstractInsnNode insn) {
        final int opc = insn.getOpcode();
        return (opc >= Opcodes.ISTORE && opc <= Opcodes.ASTORE);
    }

    public static boolean isDROP(final AbstractInsnNode insn) {
        final int opc = insn.getOpcode();
        return (opc == Opcodes.POP || opc == Opcodes.POP2);
    }

    public static boolean isExecutable(final AbstractInsnNode insn) {
        final int t = insn.getType();
        final boolean nonExec = (t == AbstractInsnNode.FRAME || t == AbstractInsnNode.LABEL || t == AbstractInsnNode.LINE);
        return !nonExec;
    }

    public static InsnNode getDrop(int size) {
        final int opc  = (size == 1) ? Opcodes.POP : Opcodes.POP2;
        return new InsnNode(opc);
    }

    /**
     *  Does the argument push a value to the stack, and pops nothing, without any side-effects?
     *  Ie the argument pushes a local-var, or a non-class constant.
     *
     *  TODO how about NEW for JDK classes without side-effecting static constructor?
     *
     *  TODO also related (although it doesn't push anything),
     *      <init> for JDK classes without side-effecting static constructor AND
     *             the instance constructor in question is known to be side-effects free.
     */
    public static boolean hasPushEffectOnly(AbstractInsnNode producer) {
        if(Util.isLOAD(producer)) return true;
        // we leave out LDC <type> on purpose.
        if(Util.isPrimitiveConstant(producer) || Util.isStringConstant(producer)) return true;
        // taking DUP to be push-effect-only leads to trouble.
        return false;
    }

    /**
     *  Is the argument a conditional jump?
     */
    public static boolean isCondJump(AbstractInsnNode insn) {
        return (insn.getType() == AbstractInsnNode.JUMP_INSN) && !isUncondJump(insn);
    }

    /**
     *  Is the argument an unconditional jump?
     */
    public static boolean isUncondJump(AbstractInsnNode insn) {
        if(insn.getType() != AbstractInsnNode.JUMP_INSN) return false;
        switch (insn.getOpcode()) {
            case Opcodes.GOTO:
            case Opcodes.LOOKUPSWITCH:
            case Opcodes.TABLESWITCH:
            case Opcodes.JSR:
                return true;
            default:
                return false;
        }
    }

    public static boolean isGOTO(AbstractInsnNode insn) {
        return (insn.getOpcode() == Opcodes.GOTO);
    }

    public static boolean isJSR(AbstractInsnNode insn) {
        return (insn.getOpcode() == Opcodes.JSR);
    }

    // ------------------------------------------------------------------------
    // instruction lookup
    // ------------------------------------------------------------------------

    /**
     *  Returns the first executable instruction (if any) occuring IN THE PROGRAM TEXT after the argument, null otherwise.
     */
    public static AbstractInsnNode execInsnAfter(AbstractInsnNode insn) {
        AbstractInsnNode current = insn;
        while(true) {
            current = current.getNext();
            if(current == null || isExecutable(current)) return current;
        }
    }

    /**
     *  Returns the executable instruction (if any) labelled by the argument, null otherwise.
     */
    public static AbstractInsnNode insnLabelledBy(final LabelNode label) {
        assert label != null;
        AbstractInsnNode labelled = label;
        while (labelled != null && labelled.getOpcode() < 0) {
            labelled = labelled.getNext();
        }
        return labelled;
    }

    /**
     *  Reports whether two LabelNodes denote in fact the same jump destination.
     */
    public static boolean denoteSameTarget(LabelNode x, LabelNode y) {
        assert x != null;
        assert y != null;

        AbstractInsnNode xTarget = insnLabelledBy(x);
        if(xTarget == null) return false;
        AbstractInsnNode yTarget = insnLabelledBy(y);
        return xTarget == yTarget;
    }

}