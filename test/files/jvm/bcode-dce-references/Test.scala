
import scala.tools.partest.BytecodeTest
import scala.tools.asm
import asm.tree.InsnList
import scala.collection.JavaConverters._

import scala.tools.asm.tree.AbstractInsnNode
import scala.tools.asm.tree.VarInsnNode

import scala.tools.asm.tree.MethodNode
import scala.tools.asm.tree.ClassNode

object Test extends BytecodeTest {

  def show: Unit = {

    val classNode = loadClassNode("DCERef_1")

    check_reassignment(classNode)
    check_nullToUninitThatGoesUnread(classNode)
    check_nullToUninitThatIsUsed(classNode)
    check_assignThisToNullSlot(classNode)
    check_assignThisToSlotWithArbitraryRef(classNode)

  }

  private def isLoad(insn: AbstractInsnNode, idx: Int): Boolean = {
    insn match {
      case vi: VarInsnNode => asm.optimiz.Util.isLOAD(vi) && (vi.`var` == idx)
      case _               => false
    }
  }

  private def isStore(insn: AbstractInsnNode, idx: Int): Boolean = {
    insn match {
      case vi: VarInsnNode => asm.optimiz.Util.isSTORE(vi) && (vi.`var` == idx)
      case _               => false
    }
  }

  private def isReturn(insn: AbstractInsnNode): Boolean = {
    insn.getOpcode == asm.Opcodes.RETURN
  }

  private def check_reassignment(classNode: ClassNode) {
    val mnode = getMethod(classNode, "reassignment")
    assert(mnode.instructions.size() == 3)
    val iter = mnode.instructions.iterator()
    assert(isLoad( iter.next(), 1))
    assert(isStore(iter.next(), 2))
    assert(isReturn(iter.next()))
  }

  private def check_nullToUninitThatGoesUnread(classNode: ClassNode) {
    val mnode = getMethod(classNode, "nullToUninitThatGoesUnread")
    assert(mnode.instructions.size() == 1)
    val insn = mnode.instructions.getFirst
    assert(isReturn(insn))
  }

  private def check_nullToUninitThatIsUsed(classNode: ClassNode) {
    val mnode = getMethod(classNode, "nullToUninitThatIsUsed")
    assert(mnode.instructions.size() == 2)
    val iter = mnode.instructions.iterator()
    assert(iter.next().getOpcode == asm.Opcodes.ACONST_NULL)
    assert(iter.next().getOpcode == asm.Opcodes.ARETURN)
  }

  private def check_assignThisToNullSlot(classNode: ClassNode) {
    val mnode = getMethod(classNode, "assignThisToNullSlot")
    assert(mnode.instructions.size() == 1)
    val iter = mnode.instructions.iterator()
    assert(isReturn(iter.next()))
  }

  private def check_assignThisToSlotWithArbitraryRef(classNode: ClassNode) {
    val mnode = getMethod(classNode, "assignThisToSlotWithArbitraryRef")
    assert(mnode.instructions.size() == 5)
    val iter = mnode.instructions.iterator()
    assert(isLoad( iter.next(), 1))
    assert(isStore(iter.next(), 2))
    assert(iter.next().getOpcode == asm.Opcodes.ACONST_NULL)
    assert(isStore(iter.next(), 2))
    assert(isReturn(iter.next()))
  }



}
