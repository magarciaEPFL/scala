/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.asm.optimiz;

import scala.tools.asm.Opcodes;
import scala.tools.asm.Type;

import scala.tools.asm.tree.AbstractInsnNode;
import scala.tools.asm.tree.LdcInsnNode;
import scala.tools.asm.tree.FieldInsnNode;

import scala.tools.asm.tree.analysis.Value;
import scala.tools.asm.tree.analysis.Interpreter;

/**
 *  Brings together in one place the size-computation that can be found e.g. in SourceInterpreter.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 */
public abstract class SizingInterpreter<V extends Value> extends Interpreter<V> implements Opcodes {

    protected SizingInterpreter(final int api) {
        super(api);
    }

    static public int getResultSize(final AbstractInsnNode insn) {
        int size;
        switch (insn.getOpcode()) {
            case LCONST_0:
            case LCONST_1:
            case DCONST_0:
            case DCONST_1:
                size = 2;
                break;
            case LDC:
                Object cst = ((LdcInsnNode) insn).cst;
                size = cst instanceof Long || cst instanceof Double ? 2 : 1;
                break;
            case GETSTATIC:
                size = Type.getType(((FieldInsnNode) insn).desc).getSize();
                break;
            case LNEG:
            case DNEG:
            case I2L:
            case I2D:
            case L2D:
            case F2L:
            case F2D:
            case D2L:
                size = 2;
                break;
            case GETFIELD:
                size = Type.getType(((FieldInsnNode) insn).desc).getSize();
                break;
            case LALOAD:
            case DALOAD:
            case LADD:
            case DADD:
            case LSUB:
            case DSUB:
            case LMUL:
            case DMUL:
            case LDIV:
            case DDIV:
            case LREM:
            case DREM:
            case LSHL:
            case LSHR:
            case LUSHR:
            case LAND:
            case LOR:
            case LXOR:
                size = 2;
                break;
            default:
                size = 1;
        }
        return size;
    }

}
