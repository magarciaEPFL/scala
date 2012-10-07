/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import scala.tools.asm.tree.AbstractInsnNode;
import scala.tools.asm.Opcodes;

/**
 *  Utilities.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class Util {

    public static boolean isLOAD(AbstractInsnNode insn) {
        return (insn.getOpcode() >= Opcodes.ILOAD  && insn.getOpcode() <= Opcodes.ALOAD);
    }

    public static boolean isSTORE(AbstractInsnNode insn) {
        return (insn.getOpcode() >= Opcodes.ISTORE && insn.getOpcode() <= Opcodes.ASTORE);
    }

}
