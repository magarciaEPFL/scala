/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import scala.tools.asm.tree.AbstractInsnNode;
import scala.tools.asm.tree.InsnNode;
import scala.tools.asm.Opcodes;

/**
 *  Utilities.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class Util {

    public static boolean isLOAD(final AbstractInsnNode insn) {
        return (insn.getOpcode() >= Opcodes.ILOAD  && insn.getOpcode() <= Opcodes.ALOAD);
    }

    public static boolean isSTORE(final AbstractInsnNode insn) {
        return (insn.getOpcode() >= Opcodes.ISTORE && insn.getOpcode() <= Opcodes.ASTORE);
    }

    public static boolean isDROP(final AbstractInsnNode insn) {
        return (insn.getOpcode() == Opcodes.POP || insn.getOpcode() == Opcodes.POP2);
    }

    public static boolean isExecutable(final AbstractInsnNode insn) {
        int t = insn.getType();
        boolean nonExec = (t == AbstractInsnNode.FRAME || t == AbstractInsnNode.LABEL || t == AbstractInsnNode.LINE);
        return !nonExec;
    }

    public static InsnNode getDrop(int size) {
        int opc  = (size == 1) ? Opcodes.POP : Opcodes.POP2;
        return new InsnNode(opc);
    }
}
