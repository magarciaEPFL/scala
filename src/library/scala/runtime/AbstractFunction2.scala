/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

abstract class AbstractFunction2[@specialized(scala.Int, scala.Long, scala.Double) -T1, @specialized(scala.Int, scala.Long, scala.Double) -T2, @specialized(scala.Unit, scala.Boolean, scala.Int, scala.Float, scala.Long, scala.Double) +R] extends Function2[T1, T2, R] {

}

final class MHAbsFun2[@specialized(scala.Int, scala.Long, scala.Double) -T1, @specialized(scala.Int, scala.Long, scala.Double) -T2, @specialized(scala.Unit, scala.Boolean, scala.Int, scala.Float, scala.Long, scala.Double) +R](target: _root_.java.lang.invoke.MethodHandle) extends AbstractFunction2[T1, T2, R] {
  def apply(v1: T1, v2: T2): R = { 
    val args = new _root_.java.util.ArrayList[Any]()
    args.add(v1)
    args.add(v2)
    target.invokeWithArguments(args).asInstanceOf[R]
 }
}
