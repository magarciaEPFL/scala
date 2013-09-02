package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes


/*
 * Check the following transformation:
 *
 * Code pattern to detect:
 *
 *         if<cond> L1 // no matter whether L1 and L2 differ or not
 *         goto L2     // no executable nor LabelNodes in between this and the previous
 *     L1:             // no executable nor LabelNodes in between this and the previous
 *
 * Rewritten into:
 *
 *         if<!cond> L2
 *     L1:
 *
 *
 * */
@RunWith(classOf[JUnit4])
class JumpReduUnit3Test {

  @Test
  def show: Unit = {
    val t   = transformed(before())
    val isa = wrapped(t)
    val isb = wrapped(after())
    assert(isa == isb)
  }

  def wrapped(m: asm.tree.MethodNode) = {
    Util.computeMaxLocalsMaxStack(m)
    Util.textify(m)
  }

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
    m.visitFieldInsn(Opcodes.GETSTATIC, "XYZ", "abc", "Ljava/lang/Object;")
    val L1 = new asm.Label
    val L2 = new asm.Label
    m.visitJumpInsn(Opcodes.IFNULL, L1)
    m.visitJumpInsn(Opcodes.GOTO,   L2)
    m.visitLabel(L1)
    m.visitLabel(L2)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def after(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    m.visitFieldInsn(Opcodes.GETSTATIC, "XYZ", "abc", "Ljava/lang/Object;")
    val L1 = new asm.Label
    val L2 = new asm.Label
    m.visitInsn(Opcodes.POP)
    m.visitLabel(L1)
    m.visitLabel(L2)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def transformed(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new JumpReducer
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform(input) } while (tr.changed)

    input
  }

}
