/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */
// GENERATED CODE: DO NOT EDIT. See scala.Function0 for timestamp.

package scala.runtime

abstract class AbstractFunction12[-T1, -T2, -T3, -T4, -T5, -T6, -T7, -T8, -T9, -T10, -T11, -T12, +R] extends Function12[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, R] {

}

final class MHAbsFun12[-T1, -T2, -T3, -T4, -T5, -T6, -T7, -T8, -T9, -T10, -T11, -T12, +R](target: _root_.java.lang.invoke.MethodHandle) extends AbstractFunction12[T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, R] {
  def apply(v1: T1, v2: T2, v3: T3, v4: T4, v5: T5, v6: T6, v7: T7, v8: T8, v9: T9, v10: T10, v11: T11, v12: T12): R = { 
    val args = new _root_.java.util.ArrayList[Any]()
    args.add(v1)
    args.add(v2)
    args.add(v3)
    args.add(v4)
    args.add(v5)
    args.add(v6)
    args.add(v7)
    args.add(v8)
    args.add(v9)
    args.add(v10)
    args.add(v11)
    args.add(v12)
    target.invokeWithArguments(args).asInstanceOf[R]
 }
}
