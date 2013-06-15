/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

final class ReflBasedFunM1[@specialized(scala.Int, scala.Long, scala.Float, scala.Double/*, scala.AnyRef*/) -T1, @specialized(scala.Unit, scala.Boolean, scala.Int, scala.Float, scala.Long, scala.Double/*, scala.AnyRef*/) +R](delegate: java.lang.reflect.Method, args: Array[Object]) extends AbstractFunction1[T1, R] {

  /** Apply the body of this function to the argument{s}.
   *  @return   the result of function application.
   */
  def apply(v1: T1): R = {
    args(1) = v1.asInstanceOf[AnyRef]
    delegate.invoke(null, args: _*).asInstanceOf[R]
  }

    
}
