package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm

import scala.tools.asm.Opcodes

@RunWith(classOf[JUnit4])
class DeadStoreElimPrimTest {

  /*
   *    (a) Replace (a STORE instruction for a local-var of primitive type which isn't live) with a DROP instruction.
   *        In particular, the initialization of (a local-var that is never read) is replaced with DROP.
   *        This rewriting doesn't lead to non-definitely-initialized errors, because the local-vars is never read anyway.
   */
  @Test
  def dropDeadStoreTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ICONST_0)
      m.visitVarInsn(Opcodes.ISTORE, 1)
      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ICONST_0)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   *    (b) Remove an IINC instruction for a non-live local.
   */
  @Test
  def removeIINCTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ICONST_0)
      m.visitVarInsn(Opcodes.ISTORE, 1)
      m.visitIincInsn(1, 1)

      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ICONST_0)
      m.visitInsn(Opcodes.POP)
      m.visitInsn(Opcodes.RETURN)

      m
    }

    compareMethods(before, after)
  }

  /*
   *    (c) Elide a STORE-LOAD pair provided the local (of primitive type) isn't used afterwards.
   *        For example:
   *           9:  istore_2
   *          10:  iload_2  // no intervening LabelNode between previous instruction and this one
   *        ie there's no consumer for the STORE instruction above other than the (immediately following) LOAD.
   */
  @Test
  def elideStoreLoadPairTest: Unit = {
    val before: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ICONST_0)
      m.visitVarInsn(Opcodes.ISTORE, 1)
      m.visitVarInsn(Opcodes.ILOAD, 1)
      m.visitInsn(Opcodes.POP)

      m.visitInsn(Opcodes.RETURN)

      m
    }
    val after: asm.tree.MethodNode = {
      val m  = mkMethodNode
      m.visitInsn(Opcodes.ICONST_0)
      m.visitInsn(Opcodes.POP)
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
    val tr = new DeadStoreElimPrim
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform("C", input) } while (tr.changed)

    input
  }

}
