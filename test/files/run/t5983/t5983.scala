import scala.tools.partest.AsmpTest

object Test extends AsmpTest {

  class IA

  class IB

  @scala.beans.BeanInfo
  case class B(a: IA, b: IB)

}
