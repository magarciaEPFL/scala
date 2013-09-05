package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm

import scala.tools.asm.Opcodes


@RunWith(classOf[JUnit4])
class JumpReducerTest {

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
   */
  @Test
  def condJumpOverUncondJumpTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitFieldInsn(Opcodes.GETSTATIC, "XYZ", "abc", "Ljava/lang/Object;")
      val b1 = new asm.Label
      m.visitJumpInsn(Opcodes.IFNULL, b1)
      m.visitJumpInsn(Opcodes.GOTO,   b1)
      m.visitLabel(b1)
      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitFieldInsn(Opcodes.GETSTATIC, "XYZ", "abc", "Ljava/lang/Object;")
      val b1 = new asm.Label
      m.visitInsn(Opcodes.POP)
      m.visitLabel(b1)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   * Check the following transformation:
   *
   * Removes a (conditional or unconditional) jump to a destination that is the next program point anyway.
   *
   */
  @Test
  def jumpToNextTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitFieldInsn(Opcodes.GETSTATIC, "XYZ", "abc", "Ljava/lang/Object;")
      val b1 = new asm.Label
      m.visitJumpInsn(Opcodes.IFNULL, b1)
      m.visitLabel(b1)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitFieldInsn(Opcodes.GETSTATIC, "XYZ", "abc", "Ljava/lang/Object;")
      val b1 = new asm.Label
      m.visitInsn(Opcodes.POP)
      m.visitLabel(b1)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

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
   */
  @Test
  def simplifyJumpsTest: Unit = {
    val before: asm.tree.MethodNode = {
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
    val after: asm.tree.MethodNode = {
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

    compareMethods(before, after)
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
    val tr = new JumpReducer
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform(input) } while (tr.changed)

    input
  }

}
