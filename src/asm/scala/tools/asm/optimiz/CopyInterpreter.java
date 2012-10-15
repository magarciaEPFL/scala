/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.asm.optimiz;

import scala.tools.asm.tree.AbstractInsnNode;

import scala.tools.asm.tree.analysis.SourceInterpreter;
import scala.tools.asm.tree.analysis.SourceValue;

/**
 * Propagates the input value in `copyOperation()`,
 * otherwise propagates a new token standing for an unknown value.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 */
public class CopyInterpreter extends SourceInterpreter
{

    @Override
    public SourceValue copyOperation(final AbstractInsnNode insn, final SourceValue value) {
        return value;
    }

}