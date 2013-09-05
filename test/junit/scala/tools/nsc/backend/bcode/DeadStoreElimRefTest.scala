package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm

import scala.tools.asm.Opcodes

@RunWith(classOf[JUnit4])
class DeadStoreElimRefTest {

  /*
   *   (a) reassignment from same ===> drop instead of store
   */
  @Test
  def reassignmentFromSameTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitVarInsn(Opcodes.ASTORE, 1)

      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitInsn(Opcodes.POP)
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   *   (b) assign RHS produced-by-ACONST_NULL to uninitialized LHS that goes unread ===> drop instead of store
   *       (assign null to null already simplified by NullnessPropagator)
   */
  @Test
  def deadNullAssignToUninitTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitVarInsn(Opcodes.ASTORE, 1)

      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   *   (c) focus on ASTORE X for X != 0 in instanceMethod, where X goes unread, where RHS is FakeParamLoad(0)
   *       Note: FakeParamLoad(0) and not ALOAD_0, the latter could give us sthg other than FakeParamLoad(0)
   *       Subcases:
   *       (c.1) LHS slot contains uninit            ===> drop instead of store
   *       ...
   */
  @Test
  def lhsUninitParamStoreTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitVarInsn(Opcodes.ASTORE, 1)

      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   *   (c) focus on ASTORE X for X != 0 in instanceMethod, where X goes unread, where RHS is FakeParamLoad(0)
   *       Note: FakeParamLoad(0) and not ALOAD_0, the latter could give us sthg other than FakeParamLoad(0)
   *       Subcases:
   *       ...
   *       (c.3) LHS slot contains only ACONST_NULL instructions as producers ===> drop instead of store
   *       ...
   */
  @Test
  def nullLhsStore: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   *   (c) focus on ASTORE X for X != 0 in instanceMethod, where X goes unread, where RHS is FakeParamLoad(0)
   *       Note: FakeParamLoad(0) and not ALOAD_0, the latter could give us sthg other than FakeParamLoad(0)
   *       Subcases:
   *       ...
   *       (c.4) LHS slot contains some other        ===> drop; ACONST_NULL; store
   */
  @Test
  def lhsContainsSomeOtherTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitFieldInsn(Opcodes.GETSTATIC, "scala/Predef$", "MODULE$", "Lscala/Predef$;")
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitFieldInsn(Opcodes.GETSTATIC, "scala/Predef$", "MODULE$", "Lscala/Predef$;")
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitVarInsn(Opcodes.ALOAD, 0)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitVarInsn(Opcodes.ASTORE, 1)
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

  def transform(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new DeadStoreElimRef
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform("C", input) } while (tr.changed)

    input
  }

}
