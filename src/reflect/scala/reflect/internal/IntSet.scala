/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.reflect.internal

final class IntSet {

  private var keytable: Array[Int] = newEmptyArray(32) // 32 is initSize
  private var sz = 0

  private def newEmptyArray(size: Int) = new Array[Int](size)

  def insert(k: Int) {
    checkResize()

    var pos  = index(k)
    val nil  = 0
    var curr = keytable(pos)

    while (curr != nil && curr != k) {
      pos = (pos + 1) % keytable.length
      curr = keytable(pos)
    }

    keytable(pos) = k
    val added = curr == nil
    if (added) sz += 1

  }

  private def checkResize() {
    val loadFactor = 450
    if (sz * 1000 / loadFactor > keytable.length) {
      val okeytable = keytable
      val ncapacity = keytable.length * 2
      keytable = newEmptyArray(ncapacity)
      sz = 0

      var pos = 0
      val nil = 0
      while (pos < okeytable.length) {
        val curr = okeytable(pos)
        if (curr != nil) {
          insert(curr)
        }
        pos += 1
      }
    }
  }

  private def before(i: Int, j: Int) = {
    val d = keytable.length >> 1
    if (i <= j) j - i < d
    else i - j > d
  }

  private def index(hc: Int): Int = {
    math.abs(scala.util.hashing.byteswap32(hc)) % keytable.length
  }

  def apply(k: Int): Boolean = {
    var pos = index(k)
    val nil = 0
    var curr = keytable(pos)

    while (curr != nil && curr != k) {
      pos = (pos + 1) % keytable.length
      curr = keytable(pos)
    }

    (curr != nil)
  }

  def +=(k: Int) {
    insert(k)
  }

  def -=(k: Int) {
    var pos  = index(k)
    val nil  = 0
    var curr = keytable(pos)

    while (curr != nil && curr != k) {
      pos = (pos + 1) % keytable.length
      curr = keytable(pos)
    }

    if (curr != nil) {

      var h0 = pos
      var h1 = (h0 + 1) % keytable.length
      while (keytable(h1) != nil) {
        val h2 = index(keytable(h1))
        if (h2 != h1 && before(h2, h0)) {
          keytable(h0) = keytable(h1)
          h0 = h1
        }
        h1 = (h1 + 1) % keytable.length
      }

      keytable(h0) = nil
      sz -= 1

    }
  }

  def clear() {
    keytable = newEmptyArray(32)  // 32 is initSize
    sz = 0
  }

  def size: Int = sz

}

