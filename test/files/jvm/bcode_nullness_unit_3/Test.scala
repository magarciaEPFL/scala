import scala.tools.nsc.backend.bcode.NullnessPropagator
import scala.tools.nsc.backend.bcode.Util
import scala.tools.partest.BytecodeTest
import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

/*
 *    (c) simplify an ASTORE both whose RHS and LHS are known to contain null (POP1 replaces it).
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
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitVarInsn(Opcodes.ASTORE, 1)
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitVarInsn(Opcodes.ASTORE, 1)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def after(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitVarInsn(Opcodes.ASTORE, 1)
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitInsn(Opcodes.POP)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def transformed(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new NullnessPropagator
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform("C", input) } while (tr.changed)

    input
  }

}
