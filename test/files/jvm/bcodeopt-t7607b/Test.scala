
import scala.tools.partest.BytecodeTest
import scala.tools.asm
import asm.tree.InsnList
import scala.collection.JavaConverters._

object Test extends BytecodeTest {

  def show: Unit = {
    val classNode = loadClassNode("C_1")
    val divIMethodNode = getMethod(classNode, "divI")
    val remIMethodNode = getMethod(classNode, "remI")

    // after optimization method bodies should have been reduced to just load the constant result to return
    assert(divIMethodNode.instructions.size() == 2)
    assert(remIMethodNode.instructions.size() == 2)
    
  }

}
