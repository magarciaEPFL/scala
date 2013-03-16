/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

abstract class AbstractFunction0[@specialized(Specializable.Primitives) +R] extends Function0[R] {

}

final class MHAbsFun0[@specialized(Specializable.Primitives) +R](target: _root_.java.lang.invoke.MethodHandle) extends AbstractFunction0[R] {
  def apply(): R = { 
    val args = new _root_.java.util.ArrayList[Any]()
    target.invokeWithArguments(args).asInstanceOf[R]
 }
}
