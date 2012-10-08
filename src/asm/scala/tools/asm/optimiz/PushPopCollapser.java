/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import scala.tools.asm.Opcodes;
import scala.tools.asm.tree.*;

import scala.tools.asm.tree.analysis.AnalyzerException;

import java.util.*;

/**
 *  Some transformations (eg DeadStoreElim) mark computations as redundant by inserting DROP instructions to discard computed values.
 *
 *  This transformation starts from there by removing those (producer, consumer) pairs where
 *  the consumer is a DROP and the producer has its value consumed only by the DROP in question.
 *  (More general cases are possible, but the above results from inlining thus this rewriting handles that scenario).
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class PushPopCollapser {

    public boolean changed = false;

    public void transform(final String owner, final MethodNode mnode) throws AnalyzerException {

        changed = false;

        // find the instructions consuming values produced by other instructions.
        ProdConsAnalyzer cp = ProdConsAnalyzer.create();
        cp.analyze(owner, mnode);
        Iterator<AbstractInsnNode> iter = mnode.instructions.iterator();

        while(iter.hasNext()) {
            AbstractInsnNode current = iter.next();
            boolean isElidable =
               (current != null      &&
                Util.isDROP(current) &&
                cp.isSoleConsumerForItsProducers(current));
            if (isElidable) {
                int size = (current.getOpcode() == Opcodes.POP ? 1 : 2);
                cp.neutralizeStackPush(current, size);
                mnode.instructions.remove(current);
                changed = true;
            }
        }
    }

}
