import scala.tools.nsc.backend.bcode.DeadStoreElimPrim
import scala.tools.nsc.backend.bcode.Util
import scala.tools.partest.BytecodeTest
import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

/*
 *    (a) Replace (a STORE instruction for a local-var of primitive type which isn't live) with a DROP instruction.
 *        In particular, the initialization of (a local-var that is never read) is replaced with DROP.
 *        This rewriting doesn't lead to non-definitely-initialized errors, because the local-vars is never read anyway.
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
    m.visitInsn(Opcodes.ICONST_0)
    m.visitVarInsn(Opcodes.ISTORE, 1)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def after(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    m.visitInsn(Opcodes.ICONST_0)
    m.visitInsn(Opcodes.POP)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def transformed(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new DeadStoreElimPrim
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform("C", input) } while (tr.changed)

    input
  }

}
