package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

@RunWith(classOf[JUnit4])
class UnBoxEliderUnit1Test {

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

  private def boxToInteger(m: asm.tree.MethodNode) {
    m.visitMethodInsn(Opcodes.INVOKESTATIC, BoxesRunTime, "boxToInteger", "(I)Ljava/lang/Integer;")
  }

  private def unboxToInt(m: asm.tree.MethodNode) {
    m.visitMethodInsn(Opcodes.INVOKESTATIC, BoxesRunTime, "unboxToInt", "(Ljava/lang/Object;)I")
  }

  def before(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    val L1 = new asm.Label
    val L2 = new asm.Label
    // control-flow split, each branch loads an Integer onto the operand stack
    m.visitVarInsn(Opcodes.ALOAD, 0)
    m.visitJumpInsn(Opcodes.IFNULL, L1)
    m.visitVarInsn(Opcodes.ILOAD, 1)
    boxToInteger(m)
    m.visitJumpInsn(Opcodes.GOTO, L2)
    m.visitLabel(L1)
    m.visitVarInsn(Opcodes.ILOAD, 1)
    boxToInteger(m)
    // control-flow merge, store into local-var and unbox
    m.visitLabel(L2)
    m.visitVarInsn(Opcodes.ASTORE, 2)
    m.visitVarInsn(Opcodes.ALOAD,  2)
    unboxToInt(m)
    m.visitVarInsn(Opcodes.ISTORE, 3)
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
    m.visitVarInsn(Opcodes.ILOAD, 1)
    // elided boxing
    m.visitJumpInsn(Opcodes.GOTO, L2)
    m.visitLabel(L1)
    m.visitVarInsn(Opcodes.ILOAD, 1)
    // elided boxing
    // control-flow merge, store into local-var and unbox
    m.visitLabel(L2)
    m.visitVarInsn(Opcodes.ISTORE, 2) // was ASTORE
    m.visitVarInsn(Opcodes.ILOAD,  2) // was ALOAD
    // elided unboxing
    m.visitVarInsn(Opcodes.ISTORE, 3)
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
