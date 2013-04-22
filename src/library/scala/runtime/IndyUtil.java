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
        final String                                serializedLCC,
        final String                                isSingletonized,
        final Class                                 hostClass
    ) throws NoSuchFieldException, NoSuchMethodException, IllegalAccessException, SecurityException
    {
        final byte[] bytes = javax.xml.bind.DatatypeConverter.parseHexBinary(serializedLCC);
        Class<?> clazz = null;
        try {
            clazz = (new DynamicLoader(hostClass)).loadFromBytes(bytes);
        } catch(Error err) {
            throw err;
        }
        java.lang.invoke.MethodHandle lambdaLoader = null;
        if(isSingletonized == null) {
            lambdaLoader = lookup.findStaticGetter(clazz, "$single", clazz);
        }
        else {
            final java.lang.reflect.Constructor ctor = clazz.getDeclaredConstructors()[0];
            lambdaLoader = lookup.unreflectConstructor(ctor);
        }
        java.lang.invoke.MethodHandle upcasted =
                lambdaLoader.asType(lambdaLoader.type().changeReturnType(clazz.getSuperclass()));
        return new java.lang.invoke.ConstantCallSite(upcasted);
    }

}