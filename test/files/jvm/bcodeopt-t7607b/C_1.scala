// SI-7607 optimizer changes behavior of IDIV, LDIV, IREM, LREM bytecode instructions when the result is dropped
class C_1 {

  def divI(b: Boolean): Int = { (if (b) 4 else 8 / 2) / (if (b) 2 else 1 + 1) }
  def remI(b: Boolean): Int = { (if (b) 4 else 8 / 2) % (if (b) 2 else 1 + 1) }

}

