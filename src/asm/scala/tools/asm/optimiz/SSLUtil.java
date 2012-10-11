/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import scala.tools.asm.Opcodes;
import scala.tools.asm.Type;
import scala.tools.asm.tree.AbstractInsnNode;
import scala.tools.asm.tree.MethodInsnNode;

/**
 *  Utilities about bytecode specific to the Scala Standard Library.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class SSLUtil {

    // ------------------------------------------------------------------------
    // utilities made available to clients
    // ------------------------------------------------------------------------

    public static boolean isSideEffectFreeCall(AbstractInsnNode producer) {
        if(isUnBox(producer) || isBox(producer)) return true;
        return false;
    }

    public static boolean isUnBox(AbstractInsnNode insn) {
      if(insn.getType()   != AbstractInsnNode.METHOD_INSN ||
         insn.getOpcode() != Opcodes.INVOKESTATIC) {
        return false;
      }

      return isUnBoxCall((MethodInsnNode)insn);
    }

    public static boolean isUnBoxCall(MethodInsnNode mi) {

        if(!mi.owner.equals(BoxesRunTime)) return false;

        Type retType = Type.getReturnType(mi.desc);

        switch (retType.getSort()) {
            case Type.BOOLEAN: return "unboxToBoolean".equals(mi.name) && "(Ljava/lang/Object;)Z".equals(mi.desc);
            case Type.BYTE:    return "unboxToByte".equals(mi.name)    && "(Ljava/lang/Object;)B".equals(mi.desc);
            case Type.CHAR:    return "unboxToChar".equals(mi.name)    && "(Ljava/lang/Object;)C".equals(mi.desc);
            case Type.SHORT:   return "unboxToShort".equals(mi.name)   && "(Ljava/lang/Object;)S".equals(mi.desc);
            case Type.INT:     return "unboxToInt".equals(mi.name)     && "(Ljava/lang/Object;)I".equals(mi.desc);
            case Type.LONG:    return "unboxToLong".equals(mi.name)    && "(Ljava/lang/Object;)J".equals(mi.desc);
            case Type.FLOAT:   return "unboxToFloat".equals(mi.name)   && "(Ljava/lang/Object;)F".equals(mi.desc);
            case Type.DOUBLE:  return "unboxToDouble".equals(mi.name)  && "(Ljava/lang/Object;)D".equals(mi.desc);

            default: return false;
        }

    }

    public static boolean isBox(AbstractInsnNode insn) {
      if(insn.getType()   != AbstractInsnNode.METHOD_INSN ||
         insn.getOpcode() != Opcodes.INVOKESTATIC) {
        return false;
      }

      return isBoxCall((MethodInsnNode)insn);
    }

    public static boolean isBoxCall(MethodInsnNode mi) {

        if(!mi.owner.equals(BoxesRunTime)) return false;

        Type[] argTs = Type.getArgumentTypes(mi.desc);
        if(argTs.length != 1) return false;

        switch (argTs[0].getSort()) {
            case Type.BOOLEAN: return "boxToBoolean".equals(mi.name)   && "(Z)Ljava/lang/Boolean;".equals(mi.desc);
            case Type.BYTE:    return "boxToByte".equals(mi.name)      && "(B)Ljava/lang/Byte;".equals(mi.desc);
            case Type.CHAR:    return "boxToCharacter".equals(mi.name) && "(C)Ljava/lang/Character;".equals(mi.desc);
            case Type.SHORT:   return "boxToShort".equals(mi.name)     && "(S)Ljava/lang/Short;".equals(mi.desc);
            case Type.INT:     return "boxToInteger".equals(mi.name)   && "(I)Ljava/lang/Integer;".equals(mi.desc);
            case Type.LONG:    return "boxToLong".equals(mi.name)      && "(J)Ljava/lang/Long;".equals(mi.desc);
            case Type.FLOAT:   return "boxToFloat".equals(mi.name)     && "(F)Ljava/lang/Float;".equals(mi.desc);
            case Type.DOUBLE:  return "boxToDouble".equals(mi.name)    && "(D)Ljava/lang/Double;".equals(mi.desc);

            default: return false;
        }

    }

    // ------------------------------------------------------------------------
    // internal methods
    // ------------------------------------------------------------------------

    private static String BoxesRunTime = "scala/runtime/BoxesRunTime";

}
