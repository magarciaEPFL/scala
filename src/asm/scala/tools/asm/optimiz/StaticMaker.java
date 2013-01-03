/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.asm.optimiz;

import java.util.*;

import scala.tools.asm.Opcodes;

import scala.tools.asm.tree.*;

import scala.tools.asm.tree.analysis.AnalyzerException;

/**
 *  (1) Find all methods fulfilling all of:
 *      private, non-constructor, non-abstract, instance, lacking usages of THIS.
 *
 *     (Therefore, those methods that would qualify except that LOAD_0 is used for self-recursion aren't made static.
 *      This is a known limitation to keep the analysis simple).
 *
 *  (2) Make them ACC_STATIC
 *
 *  (3) scan all non-abstract methods in the class being transformed, selecting all callsites to MethodNodes found above.
 *      Adapt the instructions that provide arguments for each of those callsites, dropping the receiver.
 *
 *  This transformation is useful as part of a larger code refactoring, rather than standalone.
 *
 *  As usual, care is required with code relying on private methods,
 *  including reflection or invokedynamic or a methodhandle constant.
 *
 *  Given this transformer inserts POP1 or POP2 instructions, afterwards PushPopCollapser should be run.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 */
public class StaticMaker {

    public boolean changed;

    /**
     * @return those MethodNodes which were made ACC_STATIC.
     *         Please notice other MethodNodes may also have been adapted
     *         (in order to keep callsites to the above well-formed).
     * */
    public Set<MethodNode> transform(final ClassNode cnode) throws AnalyzerException {

        changed = false;

        Set<MethodNode> methodsMadeStatic = new HashSet<MethodNode>();

        for (MethodNode m : cnode.methods) {
            if (
                 Util.isPrivateMethod(m)  &&
                !Util.isConstructor(m)    &&
                !Util.isAbstractMethod(m) &&
                !Util.isSynchronizedMethod(m) &&
                 Util.isInstanceMethod(m) &&
                 lacksUsagesOfTHIS(m)
            ) {
                changed = true;
                m.access |= Opcodes.ACC_STATIC;
                Iterator<AbstractInsnNode> insnIter = m.instructions.iterator();
                while(insnIter.hasNext()) {
                    AbstractInsnNode insn = insnIter.next();
                    if(insn.getType() == AbstractInsnNode.VAR_INSN) {
                        VarInsnNode vi = (VarInsnNode)insn;
                        vi.var -= 1;
                    }
                }
                Iterator<LocalVariableNode> lvnIter = m.localVariables.iterator();
                while(lvnIter.hasNext()) {
                    LocalVariableNode lvn = lvnIter.next();
                    if(lvn.index == 0) {
                        lvnIter.remove();
                    } else {
                        lvn.index -= 1;
                    }
                }
                Util.computeMaxLocalsMaxStack(m);
                methodsMadeStatic.add(m);
                for (MethodNode caller : cnode.methods) {
                    if (!Util.isAbstractMethod(m)) {
                        adaptCallsitesTargeting(cnode, caller, m);
                    }
                }
            }
        }

        return methodsMadeStatic;
    }

    private boolean lacksUsagesOfTHIS(final MethodNode m) {
        assert !Util.isAbstractMethod(m);
        assert  Util.isInstanceMethod(m);

        Iterator<AbstractInsnNode> iter = m.instructions.iterator();
        while(iter.hasNext()) {
            AbstractInsnNode insn = iter.next();
            if(insn.getType() == AbstractInsnNode.VAR_INSN) {
                VarInsnNode vi = (VarInsnNode)insn;
                if(vi.getOpcode() == Opcodes.RET) {
                    return false; // doing so prevents any modification
                }
                if(vi.getOpcode() == Opcodes.ALOAD || vi.getOpcode() == Opcodes.ASTORE) {
                    if(vi.var == 0) {
                        return false;
                    }
                }
            }
        }

        return true;
    }

    /**
     *  Adapt the callsites of the method just made static ("callee"), by
     *    - dropping the receiver,
     *    - changing the callsite's opcode to INVOKESTATIC.
     *
     *  @param caller a method in the class being transformed,
     *                to be adapted in case it invokes the (already made static) method callee.
     *  @param callee (private) method that was made static.
     *
     * */
    public void adaptCallsitesTargeting(final ClassNode  cnode,
                                        final MethodNode caller,
                                        final MethodNode callee) throws AnalyzerException {

        assert cnode.methods.contains(caller);
        assert cnode.methods.contains(callee);

        if(Util.isAbstractMethod(caller)) {
            return;
        }

        // find callsites
        Set<MethodInsnNode> callsites = new HashSet<MethodInsnNode>();

        Iterator<AbstractInsnNode> insnIter = caller.instructions.iterator();
        while(insnIter.hasNext()) {
            AbstractInsnNode insn = insnIter.next();
            if(insn.getType() == AbstractInsnNode.METHOD_INSN) {
                MethodInsnNode mi = (MethodInsnNode)insn;
                if((mi.owner.equals(cnode.name)) &&
                   (mi.name.equals(callee.name)) &&
                   (mi.desc.equals(callee.desc))) {

                    callsites.add(mi);
                }
            }
        }

        if(callsites.isEmpty()) {
            return;
        }

        changed = true;

        // drop receiver
        UnusedParamsElider.dropArgumentsForElidedParams(cnode, caller, callsites, callee.desc, true, Collections.EMPTY_SET);

        for(MethodInsnNode callsite : callsites) {
            callsite.setOpcode(Opcodes.INVOKESTATIC);
        }

        // not necessary to Util.computeMaxLocalsMaxStack(caller) because maxLocals was increased as need arose. maxStack doesn't change.
    }

    private boolean isThis(final int localVarIdx, final MethodNode m) {
        return (localVarIdx == 0) && Util.isInstanceMethod(m);
    }

}
