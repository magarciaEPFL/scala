import scala.tools.partest.JavapTest
import scala.tools.nsc.Settings

object Test extends JavapTest {

  override def transformSettings(s: Settings): Settings = {
    s.closureConv.value = "traditional"
    s
  }

  def code = """
    |object Betty {
    |  val ds = List(1,2,3) filter (_ % 2 == 0) map (_ * 3)
    |  def m(vs: List[Int]) = vs filter (_ % 2 != 0) map (_ * 2)
    |}
    |:javap -fun Betty
  """.stripMargin

  // two anonfuns of Betty
  override def yah(res: Seq[String]) = {
    def filtered = res filter (_ contains "public final class Betty")
    4 == filtered.size
  }
}
