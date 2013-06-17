/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

final class ReflBasedFunR0[+R](delegate: java.lang.reflect.Method, receiver: Object, args: Array[Object]) extends AbstractFunction0[R] {

  /** Apply the body of this function to the argument{s}.
   *  @return   the result of function application.
   */
  def apply(): R = {
    
    try {
      delegate.invoke(receiver, args: _*).asInstanceOf[R]
    } catch {
      case ita: java.lang.reflect.InvocationTargetException => throw ita.getCause()
    }
  }

    
}
