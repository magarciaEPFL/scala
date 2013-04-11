/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2002-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */

package scala

/**
 * An annotation that indicates the static-module or value-class thus annotated
 * will have only static members in the bytecode emitted for its module-class.
 *
 * The compiler accepts @reallyStatic occurrences provided the target module-class
 * fulfills all of the following:
 *   (1) the module-class is a static module
 *   (2) the module-class is direct subclass of AnyRef
 *   (3) the module-class extends either no interfaces or just marker interfaces
 *
 * With or without this annotation, a module-class allows accessing via MODULE$
 * the singleton in question. However, @reallyStatic results in all callsites
 * targeting that singleton being `invokestatic` instructions, ie the singleton is not loaded
 * before any arguments. This may affect when the side-effects (if any) of the
 * (static) class-initializer of the module-class become visible. In the simplest case,
 * the class-initializer of a module-class just limits itself to assigning the singleton to MODULE$.
 * But it's also possible for the class-initializer to perform more work, e.g. whenever
 * the companion-object contains statements, or defines vals or vars.
 *
 * Finally, an object annotated with @reallyStatic that also defines @inline methods
 * gives the inliner permission to replace an `invokestatic` (targeting the method in question)
 * with its body, thus potentially skipping running the class-initializer for the associated module-class.
 *
 * The caveats above are listed for completeness. When used for its intended purpose, @reallyStatic is really useful!
 *
 * Example:
 * {{{
 * @reallyStatic
 * object Hello {
 *   def sayHello(): String
 * }
 * }}}
 *
 *  @author  Miguel Garcia, http://lampwww.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @since   2.11
 */
class reallyStatic extends scala.annotation.StaticAnnotation