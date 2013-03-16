/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

abstract class AbstractFunction3[-T1, -T2, -T3, +R] extends Function3[T1, T2, T3, R] {

}

final class MHAbsFun3[-T1, -T2, -T3, +R](target: _root_.java.lang.invoke.MethodHandle) extends AbstractFunction3[T1, T2, T3, R] {
  def apply(v1: T1, v2: T2, v3: T3): R = { 
    val args = new _root_.java.util.ArrayList[Any]()
    args.add(v1)
    args.add(v2)
    args.add(v3)
    target.invokeWithArguments(args).asInstanceOf[R]
 }
}
