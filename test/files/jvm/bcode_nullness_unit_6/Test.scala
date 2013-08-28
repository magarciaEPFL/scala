import scala.tools.nsc.backend.bcode.NullnessPropagator
import scala.tools.nsc.backend.bcode.Util
import scala.tools.partest.BytecodeTest
import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

/*
 *    (f) module load is taken for non-null. In detail, the field-load won't be elided.
 *        Instead, control-flow can be simplified based on the non-nullness information.
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
    m.visitFieldInsn(Opcodes.GETSTATIC, "scala/Predef$", "MODULE$", "Lscala/Predef$;")
    val L = new asm.Label
    m.visitJumpInsn(Opcodes.IFNONNULL, L)
    m.visitLabel(L)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def after(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    m.visitFieldInsn(Opcodes.GETSTATIC, "scala/Predef$", "MODULE$", "Lscala/Predef$;")
    val L = new asm.Label
    m.visitInsn(Opcodes.POP)
    m.visitJumpInsn(Opcodes.GOTO, L)
    m.visitLabel(L)
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
