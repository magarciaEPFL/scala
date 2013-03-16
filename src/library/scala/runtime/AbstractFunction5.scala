/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

abstract class AbstractFunction5[-T1, -T2, -T3, -T4, -T5, +R] extends Function5[T1, T2, T3, T4, T5, R] {

}

final class MHAbsFun5[-T1, -T2, -T3, -T4, -T5, +R](target: _root_.java.lang.invoke.MethodHandle) extends AbstractFunction5[T1, T2, T3, T4, T5, R] {
  def apply(v1: T1, v2: T2, v3: T3, v4: T4, v5: T5): R = { 
    val args = new _root_.java.util.ArrayList[Any]()
    args.add(v1)
    args.add(v2)
    args.add(v3)
    args.add(v4)
    args.add(v5)
    target.invokeWithArguments(args).asInstanceOf[R]
 }
}
