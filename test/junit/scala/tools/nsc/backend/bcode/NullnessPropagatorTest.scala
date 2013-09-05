package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm

import scala.tools.asm.Opcodes

@RunWith(classOf[JUnit4])
class NullnessPropagatorTest {

  /*
   *    (a) simplify control-flow when a conditional jump will always be taken or avoided, for the instructions:
   *          (a.1) IF_ACMPEQ, IF_ACMPNE
   *          (a.2) IFNULL,    IFNONNULL
   */
  @Test
  def knownJumpTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      val L  = new asm.Label
      m.visitJumpInsn(Opcodes.IFNULL, L)
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitInsn(Opcodes.ATHROW)
      m.visitLabel(L)
      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitInsn(Opcodes.POP)
      val L  = new asm.Label
      m.visitJumpInsn(Opcodes.GOTO, L)
      m.visitLabel(L)
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

  /*
   *    (b) simplify an ALOAD for a local-var known to contain null (ACONST_NULL replaces it).
   *        This might enable further reductions (e.g., dead-store elimination).
   */
  @Test
  def knownNullLoadTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitVarInsn(Opcodes.ALOAD,  1)
      m.visitVarInsn(Opcodes.ASTORE, 2)
      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitVarInsn(Opcodes.ASTORE, 2)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   *    (c) simplify an ASTORE both whose RHS and LHS are known to contain null (POP1 replaces it).
   */
  @Test
  def knownNullStoreTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitVarInsn(Opcodes.ASTORE, 1)
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   *    (d) Scala unbox of null is replaced by a 0 load of the appropriate sort (I, L, F, or D).
   */
  @Test
  def unboxOfNullTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitMethodInsn(Opcodes.INVOKESTATIC, "scala/runtime/BoxesRunTime", "unboxToInt", "(Ljava/lang/Object;)I")
      m.visitVarInsn(Opcodes.ISTORE, 1)
      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.ICONST_0)
      m.visitVarInsn(Opcodes.ISTORE, 1)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   *    (e) INSTANCEOF of null replaced by POP1; ICONST_0.
   */
  @Test
  def instanceOfNullTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitTypeInsn(Opcodes.INSTANCEOF, "java/lang/Object")
      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ACONST_NULL)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.ICONST_0)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  private def mkMethodNode = {
    new asm.tree.MethodNode(Opcodes.ACC_PUBLIC, "m", "()V", null, null)
  }

  private def transform(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new NullnessPropagator
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform("C", input) } while (tr.changed)

    input
  }

}
