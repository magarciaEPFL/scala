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
 * Input:
 *
 *     IF<cond> BRANCH b1;
 *     // zero or more non-executable Nodes
 *     JUMP b1;
 *     ...
 *     b1: ...
 *
 * Output:
 *
 * The conditional branch is removed and the unconditional one left as-is.
 * The "zero or more non-executable Nodes" are also left in place,
 * because among them a jump target may exist.
 *
 * */
@RunWith(classOf[JUnit4])
class JumpReduUnit1Test {

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
    val b1 = new asm.Label
    m.visitJumpInsn(Opcodes.IFNULL, b1)
    m.visitJumpInsn(Opcodes.GOTO,   b1)
    m.visitLabel(b1)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def after(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    m.visitFieldInsn(Opcodes.GETSTATIC, "XYZ", "abc", "Ljava/lang/Object;")
    val b1 = new asm.Label
    m.visitInsn(Opcodes.POP)
    m.visitLabel(b1)
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
