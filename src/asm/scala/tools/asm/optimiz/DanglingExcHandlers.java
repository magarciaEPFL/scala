/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.asm.optimiz;

import java.util.HashSet;
import java.util.Iterator;

import scala.tools.asm.tree.*;

/**
 *  Removes redundant exception-entries,
 *  ie those protecting a range whose only executable instructions are nop.
 *  Any LineNumberNode or LabelNode in the range can be left in place,
 *  will be removed by follow-up `LabelsCleanup`
 *
 *  TODO see report Soot on exception handlers optimiz.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class DanglingExcHandlers extends MethodTransformer {

    public DanglingExcHandlers(MethodTransformer mt) {
        super(mt);
    }

    public boolean changed = false;

    public void transform(MethodNode mn) {

        changed = false;

        if(mn.tryCatchBlocks == null) { return; }

        Iterator<TryCatchBlockNode> tryIter = mn.tryCatchBlocks.iterator();
        while (tryIter.hasNext()) {
            TryCatchBlockNode tcb = tryIter.next();

            assert mn.instructions.contains(tcb.start);
            assert mn.instructions.contains(tcb.end);

            if(containsJustNops(tcb.start, tcb.end)) {
                changed = true;
                tryIter.remove();
            }
        }

        super.transform(mn);
    }

    /**
     *  Any LineNumberNode or LabelNode or FrameNode will be skipped.
     */
    public boolean containsJustNops(LabelNode start, LabelNode end) {
        assert start != null;
        assert end   != null;

        AbstractInsnNode current = start;
        while(current != end) {
          if(current.getOpcode() > 0) {
              return false;
          }
          current = current.getNext();
        }

        return true;
    }

}
