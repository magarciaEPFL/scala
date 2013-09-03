import scala.tools.nsc.backend.bcode.ConstantFolder
import scala.tools.partest.BytecodeTest
import scala.tools.asm
import scala.collection.JavaConverters._

import scala.tools.asm.Opcodes

object Test extends BytecodeTest {

  val inputClass = "Foo_1"

  def show: Unit = {
    val classNode  = loadClassNode(inputClass)
    compare(classNode, "pre1", "post1")
    compare(classNode, "pre2", "post2")
  }

  def compare(classNode: asm.tree.ClassNode, strA: String, strB: String) {
    val pre  = getMethod(classNode, "pre1")
    val post = getMethod(classNode, "post1")

    val t   = transformed(pre)
    val isa = wrapped(t)
    val isb = wrapped(post)

    assert(isa == isb)
  }

  def wrapped(m: asm.tree.MethodNode) = instructions.fromMethod(m)

  def transformed(input: asm.tree.MethodNode): asm.tree.MethodNode = {
    val tr = new ConstantFolder
    tr.transform(inputClass, input)
    // do { tr.transform(inputClass, input) } while (tr.changed)

    input
  }

}
