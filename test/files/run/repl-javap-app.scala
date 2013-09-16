
import scala.tools.partest.ReplTest

object MyApp extends App {
  Console println "Hello, delayed world."
}

// The check file contains output obtained via `:javap -app MyApp$`
// which includes constant pool indices. Compiling the test
// under -Ybackend:GenBCode removes redundant code,
// with the consequence that the constant pool isn't laid out
// anymore as for classfiles emitted by GenASM (in general
// and in the case at hand).

object Test extends ReplTest {
  def code = ":javap -app MyApp$"
}
