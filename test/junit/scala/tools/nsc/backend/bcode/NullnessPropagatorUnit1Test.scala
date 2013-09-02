package scala.tools.nsc.backend.bcode

import org.junit.Assert._
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.JUnit4

import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

/*
 *    (a) simplify control-flow when a conditional jump will always be taken or avoided, for the instructions:
 *          (a.1) IF_ACMPEQ, IF_ACMPNE
 *          (a.2) IFNULL,    IFNONNULL
 */
@RunWith(classOf[JUnit4])
class NullnessPropagatorUnit1Test {

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
    val L  = new asm.Label
    m.visitJumpInsn(Opcodes.IFNULL, L)
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitInsn(Opcodes.ATHROW)
    m.visitLabel(L)
    m.visitInsn(Opcodes.RETURN)

    m
  }

  def after(): asm.tree.MethodNode = {
    val m  = mkMethodNode
    m.visitInsn(Opcodes.ACONST_NULL)
    m.visitInsn(Opcodes.POP)
    val L  = new asm.Label
    m.visitJumpInsn(Opcodes.GOTO, L)
    m.visitLabel(L)
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
