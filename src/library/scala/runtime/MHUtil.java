/*                     __                                               *\
**     ________ ___   / /  ___     Scala API                            **
**    / __/ __// _ | / /  / _ |    (c) 2006-2013, LAMP/EPFL             **
**  __\ \/ /__/ __ |/ /__/ __ |    http://scala-lang.org/               **
** /____/\___/_/ |_/____/_/ | |                                         **
**                          |/                                          **
\*                                                                      */



package scala.runtime;

import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;

/**
  * Utilities to bind arguments to a MethodHandle, as needed in connection with s.r.MHAbsFun
  *
  * @author  Miguel Garcia, http://lampwww.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
  * @version 1.0
  *
  * */
public final class MHUtil {

    private MHUtil() { }  // do not instantiate

    /**
     * Returns either:
     *   (1) a new method handle that requires one less argument than the one received as input.
     *   (2) the same method handle
     * The first case applies when the argument pos indicates
     * a non-negative (zero-based) position where to bind the value given by the first argument.
     * Otherwise the second case.
     * */
    public static MethodHandle bindAt(int i, MethodHandle mh, int pos) {
        if(pos == -1) return mh;
        return MethodHandles.insertArguments(mh, pos, i);
    }

    /**
     * Returns either:
     *   (1) a new method handle that requires one less argument than the one received as input.
     *   (2) the same method handle
     * The first case applies when the argument pos indicates
     * a non-negative (zero-based) position where to bind the value given by the first argument.
     * Otherwise the second case.
     * */
    public static MethodHandle bindAt(long j, MethodHandle mh, int pos) {
        if(pos == -1) return mh;
        return MethodHandles.insertArguments(mh, pos, j);
    }

    /**
     * Returns either:
     *   (1) a new method handle that requires one less argument than the one received as input.
     *   (2) the same method handle
     * The first case applies when the argument pos indicates
     * a non-negative (zero-based) position where to bind the value given by the first argument.
     * Otherwise the second case.
     * */
    public static MethodHandle bindAt(float f, MethodHandle mh, int pos) {
        if(pos == -1) return mh;
        return MethodHandles.insertArguments(mh, pos, f);
    }

    /**
     * Returns either:
     *   (1) a new method handle that requires one less argument than the one received as input.
     *   (2) the same method handle
     * The first case applies when the argument pos indicates
     * a non-negative (zero-based) position where to bind the value given by the first argument.
     * Otherwise the second case.
     * */
    public static MethodHandle bindAt(double d, MethodHandle mh, int pos) {
        if(pos == -1) return mh;
        return MethodHandles.insertArguments(mh, pos, d);
    }

    /**
     * Returns either:
     *   (1) a new method handle that requires one less argument than the one received as input.
     *   (2) the same method handle
     * The first case applies when the argument pos indicates
     * a non-negative (zero-based) position where to bind the value given by the first argument.
     * Otherwise the second case.
     * */
    public static MethodHandle bindAt(boolean z, MethodHandle mh, int pos) {
        if(pos == -1) return mh;
        return MethodHandles.insertArguments(mh, pos, z);
    }

    /**
     * Returns either:
     *   (1) a new method handle that requires one less argument than the one received as input.
     *   (2) the same method handle
     * The first case applies when the argument pos indicates
     * a non-negative (zero-based) position where to bind the value given by the first argument.
     * Otherwise the second case.
     * */
    public static MethodHandle bindAt(char c, MethodHandle mh, int pos) {
        if(pos == -1) return mh;
        return MethodHandles.insertArguments(mh, pos, c);
    }

    /**
     * Returns either:
     *   (1) a new method handle that requires one less argument than the one received as input.
     *   (2) the same method handle
     * The first case applies when the argument pos indicates
     * a non-negative (zero-based) position where to bind the value given by the first argument.
     * Otherwise the second case.
     * */
    public static MethodHandle bindAt(byte b, MethodHandle mh, int pos) {
        if(pos == -1) return mh;
        return MethodHandles.insertArguments(mh, pos, b);
    }

    /**
     * Returns either:
     *   (1) a new method handle that requires one less argument than the one received as input.
     *   (2) the same method handle
     * The first case applies when the argument pos indicates
     * a non-negative (zero-based) position where to bind the value given by the first argument.
     * Otherwise the second case.
     * */
    public static MethodHandle bindAt(short s, MethodHandle mh, int pos) {
        if(pos == -1) return mh;
        return MethodHandles.insertArguments(mh, pos, s);
    }

    /**
     * Returns either:
     *   (1) a new method handle that requires one less argument than the one received as input.
     *   (2) the same method handle
     * The first case applies when the argument pos indicates
     * a non-negative (zero-based) position where to bind the value given by the first argument.
     * Otherwise the second case.
     * */
    public static MethodHandle bindAt(Object o, MethodHandle mh, int pos) {
        if(pos == -1) return mh;
        return MethodHandles.insertArguments(mh, pos, o);
    }

}
