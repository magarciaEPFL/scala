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

/**
 *  Utilities.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class Util {

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

    public static boolean hasPushEffectOnly(AbstractInsnNode producer) {
        if(Util.isLOAD(producer)) return true;
        // we leave out LDC <type> on purpose.
        if(Util.isPrimitiveConstant(producer) || Util.isStringConstant(producer)) return true;
        // TODO DUP
        // TODO check whether a NEW has no side-effects (via constructors).
        return false;
    }

}
