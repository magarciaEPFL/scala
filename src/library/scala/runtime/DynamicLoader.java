/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.runtime;

public class DynamicLoader extends java.security.SecureClassLoader
{

    public DynamicLoader(final Class cl)
    {
        super(cl.getClassLoader());
    }

    public Class<?> loadFromBytes(byte[] bytes)
    {
        final Class<?> clazz = defineClass(null, bytes, 0, bytes.length);
        resolveClass(clazz);
        return clazz;
    }

}
