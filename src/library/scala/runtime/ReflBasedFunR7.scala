/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

final class ReflBasedFunR7[-T1, -T2, -T3, -T4, -T5, -T6, -T7, +R](delegate: java.lang.reflect.Method, receiver: Object, args: Array[Object]) extends AbstractFunction7[T1, T2, T3, T4, T5, T6, T7, R] {

  /** Apply the body of this function to the argument{s}.
   *  @return   the result of function application.
   */
  def apply(v1: T1, v2: T2, v3: T3, v4: T4, v5: T5, v6: T6, v7: T7): R = {
    val cargs = args.clone()
    cargs(0) = v1.asInstanceOf[AnyRef]
    cargs(1) = v2.asInstanceOf[AnyRef]
    cargs(2) = v3.asInstanceOf[AnyRef]
    cargs(3) = v4.asInstanceOf[AnyRef]
    cargs(4) = v5.asInstanceOf[AnyRef]
    cargs(5) = v6.asInstanceOf[AnyRef]
    cargs(6) = v7.asInstanceOf[AnyRef]
    try {
      delegate.invoke(receiver, cargs: _*).asInstanceOf[R]
    } catch {
      case ite: java.lang.reflect.InvocationTargetException => throw ite.getCause()
    }
  }

    
}
