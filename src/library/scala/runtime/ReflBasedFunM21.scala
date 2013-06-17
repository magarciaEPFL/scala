/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

final class ReflBasedFunM21[-T1, -T2, -T3, -T4, -T5, -T6, -T7, -T8, -T9, -T10, -T11, -T12, -T13, -T14, -T15, -T16, -T17, -T18, -T19, -T20, -T21, +R](delegate: java.lang.reflect.Method, args: Array[Object]) extends AbstractFunction21[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, R] {

  /** Apply the body of this function to the argument{s}.
   *  @return   the result of function application.
   */
  def apply(v1: T1, v2: T2, v3: T3, v4: T4, v5: T5, v6: T6, v7: T7, v8: T8, v9: T9, v10: T10, v11: T11, v12: T12, v13: T13, v14: T14, v15: T15, v16: T16, v17: T17, v18: T18, v19: T19, v20: T20, v21: T21): R = {
    args(1) = v1.asInstanceOf[AnyRef]
    args(2) = v2.asInstanceOf[AnyRef]
    args(3) = v3.asInstanceOf[AnyRef]
    args(4) = v4.asInstanceOf[AnyRef]
    args(5) = v5.asInstanceOf[AnyRef]
    args(6) = v6.asInstanceOf[AnyRef]
    args(7) = v7.asInstanceOf[AnyRef]
    args(8) = v8.asInstanceOf[AnyRef]
    args(9) = v9.asInstanceOf[AnyRef]
    args(10) = v10.asInstanceOf[AnyRef]
    args(11) = v11.asInstanceOf[AnyRef]
    args(12) = v12.asInstanceOf[AnyRef]
    args(13) = v13.asInstanceOf[AnyRef]
    args(14) = v14.asInstanceOf[AnyRef]
    args(15) = v15.asInstanceOf[AnyRef]
    args(16) = v16.asInstanceOf[AnyRef]
    args(17) = v17.asInstanceOf[AnyRef]
    args(18) = v18.asInstanceOf[AnyRef]
    args(19) = v19.asInstanceOf[AnyRef]
    args(20) = v20.asInstanceOf[AnyRef]
    args(21) = v21.asInstanceOf[AnyRef]
    try {
      delegate.invoke(null, args: _*).asInstanceOf[R]
    } catch {
      case ita: java.lang.reflect.InvocationTargetException => throw ita.getCause()
    }
  }

    
}
