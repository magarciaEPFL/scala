package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

@RunWith(classOf[JUnit4])
class UnBoxEliderUnit3Test {

  val BoxesRunTime = "scala/runtime/BoxesRunTime"

  @Test
  def show: Unit = {
    val isa = wrapped(transformed(before()))
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

  private def boxToLong(m: asm.tree.MethodNode) {
    m.visitMethodInsn(Opcodes.INVOKESTATIC, BoxesRunTime, "boxToLong", "(J)Ljava/lang/Long;")
  }

  private def unboxToLong(m: asm.tree.MethodNode) {
    m.visitMethodInsn(Opcodes.INVOKESTATIC, BoxesRunTime, "unboxToLong", "(Ljava/lang/Object;)J")
  }

  def before(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    val L1 = new asm.Label
    val L2 = new asm.Label
    // control-flow split, each branch loads an Integer onto the operand stack
    m.visitVarInsn(Opcodes.ALOAD, 0)
    m.visitJumpInsn(Opcodes.IFNULL, L1)
    m.visitVarInsn(Opcodes.LLOAD, 1)
    boxToLong(m)
    m.visitJumpInsn(Opcodes.GOTO, L2)
    m.visitLabel(L1)
    m.visitVarInsn(Opcodes.LLOAD, 1)
    boxToLong(m)
    // control-flow merge, store into local-var and unbox
    m.visitLabel(L2)
    m.visitVarInsn(Opcodes.ASTORE, 3)
    m.visitVarInsn(Opcodes.ALOAD,  3)
    unboxToLong(m)
    m.visitVarInsn(Opcodes.LSTORE, 4)
    //     return
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def after(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    val L1 = new asm.Label
    val L2 = new asm.Label
    // control-flow split, each branch loads an int onto the operand stack
    m.visitVarInsn(Opcodes.ALOAD, 0)
    m.visitJumpInsn(Opcodes.IFNULL, L1)
    m.visitVarInsn(Opcodes.LLOAD, 1)
    // elided boxing
    m.visitJumpInsn(Opcodes.GOTO, L2)
    m.visitLabel(L1)
    m.visitVarInsn(Opcodes.LLOAD, 1)
    // elided boxing
    // control-flow merge, store into local-var and unbox
    m.visitLabel(L2)
    m.visitVarInsn(Opcodes.LSTORE, 6) // was ASTORE, had to use a not-yet-in-use local-var-idx
    m.visitVarInsn(Opcodes.LLOAD,  6) // was ALOAD
    // elided unboxing
    m.visitVarInsn(Opcodes.LSTORE, 4)
    //     return
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def transformed(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val jcc = new UnBoxElider
    Util.computeMaxLocalsMaxStack(input)
    do { jcc.transform("C", input) } while (jcc.changed)

    input
  }

}
