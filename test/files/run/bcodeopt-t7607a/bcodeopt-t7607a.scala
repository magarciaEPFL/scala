// SI-7607 optimizer changes behavior of IDIV, LDIV, IREM, LREM bytecode instructions when the result is dropped
object Test {

  def main(args: Array[String]) {

    assert(checkNoSwallow(1  / 0 ))
    assert(checkNoSwallow(1L / 0L))
    assert(checkNoSwallow(1  % 0 ))
    assert(checkNoSwallow(1L % 0L))

  }

  def checkNoSwallow[T](op: => T): Boolean = {
    try {
      op; false
    } catch {
      case ae: _root_.java.lang.ArithmeticException => true
    }
  }

}

