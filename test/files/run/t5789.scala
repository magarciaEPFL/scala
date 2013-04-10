
import scala.tools.nsc._
import interpreter.ILoop
import scala.tools.partest.ReplTest


object Test extends ReplTest {
  override def extraSettings = "-neo:o2"
  def code = """
    val n = 2
    () => n
  """
}

