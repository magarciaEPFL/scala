/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

abstract class AbstractFunction1[@specialized(scala.Int, scala.Long, scala.Float, scala.Double/*, scala.AnyRef*/) -T1, @specialized(scala.Unit, scala.Boolean, scala.Int, scala.Float, scala.Long, scala.Double/*, scala.AnyRef*/) +R] extends Function1[T1, R] {

}

final class MHAbsFun1[@specialized(scala.Int, scala.Long, scala.Float, scala.Double/*, scala.AnyRef*/) -T1, @specialized(scala.Unit, scala.Boolean, scala.Int, scala.Float, scala.Long, scala.Double/*, scala.AnyRef*/) +R](target: _root_.java.lang.invoke.MethodHandle) extends AbstractFunction1[T1, R] {
  def apply(v1: T1): R = { 
    val args = new _root_.java.util.ArrayList[Any]()
    args.add(v1)
    target.invokeWithArguments(args).asInstanceOf[R]
 }
}
