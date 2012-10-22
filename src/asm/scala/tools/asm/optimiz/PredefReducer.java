/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.asm.optimiz;

import scala.tools.asm.Opcodes;

import scala.tools.asm.tree.AbstractInsnNode;
import scala.tools.asm.tree.MethodNode;
import scala.tools.asm.tree.VarInsnNode;

import scala.tools.asm.tree.analysis.AnalyzerException;
import scala.tools.asm.tree.analysis.Analyzer;
import scala.tools.asm.tree.analysis.Frame;
import scala.tools.asm.tree.analysis.SourceValue;
import scala.tools.asm.tree.analysis.SourceInterpreter;

/**
 *
 *  TODO "Autoboxing" and "Autounboxing"
 *
 *     The following bunch of Predef definitions aren't marked @inline:
 *
 *         implicit def int2Integer(x: Int) = java.lang.Integer.valueOf(x)
 *         ...
 *         implicit def Integer2int(x: java.lang.Integer): Int = x.intValue
 *
 *     and as a result they show up in bytecode as follows:
 *
 *         getstatic      ; //Field scala/Predef$.MODULE$:Lscala/Predef$;
 *         int-load
 *         invokevirtual  ; //Method scala/Predef$.int2Integer:(I)Ljava/lang/Integer;
 *
 *     The code pattern above can be reduced to just:
 *
 *         getstatic      ; //Field scala/Predef$.MODULE$:Lscala/Predef$;
 *         POP
 *         int-load
 *         invokestatic   ; //Method java/lang/Integer.valueOf:(Ljava/lang/Integer;)I
 *
 *     (similarly for other types, and for unbox).
 *
 *     With that, UnBoxElider is given opportunity to further reduce the code.
 *
 *  TODO "GETSTATIC of scala/Predef$.MODULE$ considered side-effect free"
 *
 *     The following should cancel out:
 *
 *         getstatic    ; //Field scala/Predef$.MODULE$:Lscala/Predef$;
 *         POP
 *
 *
 */
public class PredefReducer {

    /** after transform() has run, this field records whether
     *  at least one pass of this transformer modified something. */
    public boolean changed = false;

    public void transform(final String owner, final MethodNode mnode) throws AnalyzerException {

        final ProdConsAnalyzer propag = ProdConsAnalyzer.create();
        propag.analyze(owner, mnode);

        Frame<SourceValue>[] frames = propag.getFrames();
        AbstractInsnNode[]   insns  = mnode.instructions.toArray();

        changed = false;

        int i = 0;
        while(i < insns.length) {
            i += 1;
        }

    }

}
