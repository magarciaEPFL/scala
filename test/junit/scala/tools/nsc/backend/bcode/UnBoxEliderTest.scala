package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm

import scala.tools.asm.Opcodes

@RunWith(classOf[JUnit4])
class UnBoxEliderTest {

  val BoxesRunTime = "scala/runtime/BoxesRunTime"

  @Test
  def manyBranchesOneMergeCopyTest: Unit = {
    val before: asm.tree.MethodNode = {
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

    val after: asm.tree.MethodNode = {
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

    compareMethods(before, after)
  }

  @Test
  def manyBranchesOneMergeWithoutCopyTest: Unit = {
    val before: asm.tree.MethodNode = {
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
      // control-flow merge, unbox
      m.visitLabel(L2)
      unboxToInt(m)
      m.visitVarInsn(Opcodes.ISTORE, 3)
      //     return
      m.visitInsn(Opcodes.RETURN)

      m
    }

    val after: asm.tree.MethodNode = {
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
      // elided unboxing
      m.visitVarInsn(Opcodes.ISTORE, 3)
      //     return
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  private def boxToLong(m: asm.tree.MethodNode) {
    m.visitMethodInsn(Opcodes.INVOKESTATIC, BoxesRunTime, "boxToLong", "(J)Ljava/lang/Long;")
  }

  private def unboxToLong(m: asm.tree.MethodNode) {
    m.visitMethodInsn(Opcodes.INVOKESTATIC, BoxesRunTime, "unboxToLong", "(Ljava/lang/Object;)J")
  }

  @Test
  def longVarWasBoxedTest: Unit = {
    val before: asm.tree.MethodNode = {
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

    val after: asm.tree.MethodNode = {
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

    compareMethods(before, after)
  }

  private def boxToInteger(m: asm.tree.MethodNode) {
    m.visitMethodInsn(Opcodes.INVOKESTATIC, BoxesRunTime, "boxToInteger", "(I)Ljava/lang/Integer;")
  }

  private def unboxToInt(m: asm.tree.MethodNode) {
    m.visitMethodInsn(Opcodes.INVOKESTATIC, BoxesRunTime, "unboxToInt", "(Ljava/lang/Object;)I")
  }

  private def compareMethods(before: asm.tree.MethodNode, after: asm.tree.MethodNode): Unit = {
    BytecodeAssert.assertNotEquals(before, after)
    val transformed = transform(before)
    BytecodeAssert.assertEquals(transformed, after)
  }

  private def mkMethodNode = {
    new asm.tree.MethodNode(Opcodes.ACC_PUBLIC, "m", "()V", null, null)
  }

  private def transform(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new UnBoxElider
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform("C", input) } while (tr.changed)

    input
  }

}
