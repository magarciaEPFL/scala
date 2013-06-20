/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

final class ReflBasedFunM13[-T1, -T2, -T3, -T4, -T5, -T6, -T7, -T8, -T9, -T10, -T11, -T12, -T13, +R](delegate: java.lang.reflect.Method, args: Array[Object]) extends AbstractFunction13[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, R] {

  /** Apply the body of this function to the argument{s}.
   *  @return   the result of function application.
   */
  def apply(v1: T1, v2: T2, v3: T3, v4: T4, v5: T5, v6: T6, v7: T7, v8: T8, v9: T9, v10: T10, v11: T11, v12: T12, v13: T13): R = {
    val cargs = args.clone()
    cargs(1) = v1.asInstanceOf[AnyRef]
    cargs(2) = v2.asInstanceOf[AnyRef]
    cargs(3) = v3.asInstanceOf[AnyRef]
    cargs(4) = v4.asInstanceOf[AnyRef]
    cargs(5) = v5.asInstanceOf[AnyRef]
    cargs(6) = v6.asInstanceOf[AnyRef]
    cargs(7) = v7.asInstanceOf[AnyRef]
    cargs(8) = v8.asInstanceOf[AnyRef]
    cargs(9) = v9.asInstanceOf[AnyRef]
    cargs(10) = v10.asInstanceOf[AnyRef]
    cargs(11) = v11.asInstanceOf[AnyRef]
    cargs(12) = v12.asInstanceOf[AnyRef]
    cargs(13) = v13.asInstanceOf[AnyRef]
    try {
      delegate.invoke(null, cargs: _*).asInstanceOf[R]
    } catch {
      case ite: java.lang.reflect.InvocationTargetException => throw ite.getCause()
    }
  }

    
}
