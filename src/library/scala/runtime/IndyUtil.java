/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.runtime;

/**
 *  Utilities around JSR-292 (invokedynamic and MethodHandles).
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class IndyUtil {

    /*
     * This bootstrap method is referred to by all the invokedynamic callsites
     * that requrest an instance of a Late-Closure-Class.
     * The bootstrap returns a j.l.i.ConstantCallsite which upon invocation loads onto the operand stack
     * an instance of the dclosure given by the MethodHandle `lambdaLoader` (a constant, actually).
     *
     */
    public static java.lang.invoke.CallSite bootstrapLCC
    (
        final java.lang.invoke.MethodHandles.Lookup lookup,
        final java.lang.String                      name,
        final java.lang.invoke.MethodType           type,
        final java.lang.invoke.MethodHandle         lambdaLoader
    ) {
      return new java.lang.invoke.ConstantCallSite(lambdaLoader);
    }

}