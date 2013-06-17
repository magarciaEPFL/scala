/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

final class ReflBasedFunM5[-T1, -T2, -T3, -T4, -T5, +R](delegate: java.lang.reflect.Method, args: Array[Object]) extends AbstractFunction5[T1, T2, T3, T4, T5, R] {

  /** Apply the body of this function to the argument{s}.
   *  @return   the result of function application.
   */
  def apply(v1: T1, v2: T2, v3: T3, v4: T4, v5: T5): R = {
    args(1) = v1.asInstanceOf[AnyRef]
    args(2) = v2.asInstanceOf[AnyRef]
    args(3) = v3.asInstanceOf[AnyRef]
    args(4) = v4.asInstanceOf[AnyRef]
    args(5) = v5.asInstanceOf[AnyRef]
    try {
      delegate.invoke(null, args: _*).asInstanceOf[R]
    } catch {
      case ita: java.lang.reflect.InvocationTargetException => throw ita.getCause()
    }
  }

    
}
