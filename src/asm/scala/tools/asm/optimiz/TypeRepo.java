/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.asm.optimiz;

import scala.tools.asm.tree.FieldInsnNode;

public interface TypeRepo {
    public boolean isLoadModule(FieldInsnNode fi);
}
