package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

/*
 *    (b) simplify an ALOAD for a local-var known to contain null (ACONST_NULL replaces it).
 *        This might enable further reductions (e.g., dead-store elimination).
 */
@RunWith(classOf[JUnit4])
class NullnessPropagatorUnit2Test {

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
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitVarInsn(Opcodes.ASTORE, 1)
    m.visitVarInsn(Opcodes.ALOAD,  1)
    m.visitVarInsn(Opcodes.ASTORE, 2)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def after(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitVarInsn(Opcodes.ASTORE, 1)
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitVarInsn(Opcodes.ASTORE, 2)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def transformed(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new NullnessPropagator
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform("C", input) } while (tr.changed)

    input
  }

}
