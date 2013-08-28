import scala.tools.nsc.backend.bcode.DeadStoreElimRef
import scala.tools.nsc.backend.bcode.Util
import scala.tools.partest.BytecodeTest
import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

/*
 *   (c) focus on ASTORE X for X != 0 in instanceMethod, where X goes unread, where RHS is FakeParamLoad(0)
 *       Note: FakeParamLoad(0) and not ALOAD_0, the latter could give us sthg other than FakeParamLoad(0)
 *       Subcases:
 *       ...
 *       (c.3) LHS slot contains only ACONST_NULL instructions as producers ===> drop instead of store
 *       ...
 */
object Test extends BytecodeTest {

  def show: Unit = {
    val t   = transformed(before())
    val isa = wrapped(t)
    val isb = wrapped(after())
    assert(isa == isb)
  }

  def wrapped(m: asm.tree.MethodNode) = instructions.fromMethod(m)

  def mkMethodNode = {
    new asm.tree.MethodNode(
      Opcodes.ACC_PUBLIC,
      "m",
      "()V",
      null, null
    )
  }

  def before(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    m.visitVarInsn(Opcodes.ALOAD, 0)
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitVarInsn(Opcodes.ASTORE, 1)
    m.visitVarInsn(Opcodes.ASTORE, 1)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def after(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    m.visitVarInsn(Opcodes.ALOAD, 0)
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitInsn(Opcodes.POP)
    m.visitInsn(Opcodes.POP)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def transformed(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new DeadStoreElimRef
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform("C", input) } while (tr.changed)

    input
  }

}
