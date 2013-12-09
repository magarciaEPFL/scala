import scala.tools.nsc.backend.bcode.{PushPopCollapser, Util}
import scala.tools.nsc.backend.bcode.Util
import scala.tools.partest.BytecodeTest
import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

/*
 *   Back-percolate a DROP instruction back to all its producers.
 */
object Test extends BytecodeTest {

  val inputClass = "Foo_1$"

  def show: Unit = {
    val classNode = loadClassNode(inputClass)
    val before    = getMethod(classNode, "pre1")
    val txtAfter  = Util.textify(transformed(before))

    println(txtAfter)
  }

  def transformed(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new PushPopCollapser
    Util.computeMaxLocalsMaxStack(input)
    do { tr.transform(inputClass, input) } while (tr.changed)

    input
  }

}
