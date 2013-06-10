
import scala.tools.partest.BytecodeTest
import scala.tools.asm
import asm.tree.InsnList
import scala.collection.JavaConverters._
import asm.optimiz.Util

object Test extends BytecodeTest {

  def show: Unit = {
    val classNode = loadClassNode("DSE_1")
    val methodNode = getMethod(classNode, "main")
    // after optimization there should be no STOREs
    val expected = 0

    val got = countStores(methodNode.instructions)
    assert(got == expected, s"expected $expected but got $got stores")
  }

  def countStores(insnList: InsnList): Int = {
    insnList.iterator.asScala count { insn => Util.isSTORE(insn) }
  }

}
