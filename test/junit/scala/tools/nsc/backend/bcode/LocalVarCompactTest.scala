package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm

import scala.tools.asm.Opcodes

@RunWith(classOf[JUnit4])
class LocalVarCompactTest {

  val BoxesRunTime = "scala/runtime/BoxesRunTime"

  @Test
  def compactingTest: Unit = {
    val before: asm.tree.MethodNode = {
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
      m.visitVarInsn(Opcodes.LSTORE, 5) // was ASTORE, had to use a not-yet-in-use local-var-idx
      m.visitVarInsn(Opcodes.LLOAD,  5) // was ALOAD
      // elided unboxing
      m.visitVarInsn(Opcodes.LSTORE, 3)
      //     return
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  private def mkMethodNode = {
    new asm.tree.MethodNode(Opcodes.ACC_PUBLIC, "m", "()V", null, null)
  }

  private def compareMethods(before: asm.tree.MethodNode, after: asm.tree.MethodNode): Unit = {
    BytecodeAssert.assertNotEquals(before, after)
    val transformed = transform(before)
    BytecodeAssert.assertEquals(transformed, after)
  }

  def transform(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new LocalVarCompact
    Util.computeMaxLocalsMaxStack(input)
    tr.transform(input)

    input
  }

}
