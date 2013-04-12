/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.nsc
package backend.jvm

import scala.tools.asm
import scala.annotation.switch
import scala.collection.{ immutable, mutable }
import scala.tools.nsc.io.AbstractFile
import collection.convert.Wrappers.JListWrapper

/*
 *  Based on ASM's Type class. Namer's chrs is used in this class for the same purposes as the `buf` char array in asm.Type.
 *
 *  All methods of this classs can-multi-thread
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded
 */
class BType(val bits: Long) extends AnyVal {

  @inline private def hi: Int = (bits >> 32).asInstanceOf[Int]
  @inline private def lo: Int = bits.asInstanceOf[Int]

  @inline final def off:  Int = lo
  @inline final def len:  Int = (hi & 0x00FFFFFF)
  @inline final def sort: Int = (hi >> 24)

  /*
   * can-multi-thread
   */
  def toASMType(implicit bct: BCodeTypes) : scala.tools.asm.Type = {
    import scala.tools.asm
    (sort: @switch) match {
      case asm.Type.VOID    => asm.Type.VOID_TYPE
      case asm.Type.BOOLEAN => asm.Type.BOOLEAN_TYPE
      case asm.Type.CHAR    => asm.Type.CHAR_TYPE
      case asm.Type.BYTE    => asm.Type.BYTE_TYPE
      case asm.Type.SHORT   => asm.Type.SHORT_TYPE
      case asm.Type.INT     => asm.Type.INT_TYPE
      case asm.Type.FLOAT   => asm.Type.FLOAT_TYPE
      case asm.Type.LONG    => asm.Type.LONG_TYPE
      case asm.Type.DOUBLE  => asm.Type.DOUBLE_TYPE
      case asm.Type.ARRAY   |
           asm.Type.OBJECT  => asm.Type.getObjectType(getInternalName)
      case asm.Type.METHOD  => asm.Type.getMethodType(getDescriptor)
    }
  }

  /*
   * Unlike for ICode's REFERENCE, isBoxedType(t) implies isReferenceType(t)
   * Also, `isReferenceType(RT_NOTHING) == true` , similarly for RT_NULL.
   * Use isNullType() , isNothingType() to detect Nothing and Null.
   *
   * can-multi-thread
   */
  def hasObjectSort = (sort == asm.Type.OBJECT)

  /*
   * Returns the number of dimensions of this array type. This method should
   * only be used for an array type.
   *
   * @return the number of dimensions of this array type.
   *
   * can-multi-thread
   */
  def getDimensions(implicit bct: BCodeTypes): Int = {
    var i = 1
    while (bct.global.chrs(off + i) == '[') {
      i += 1
    }
    i
  }

  /*
   * Returns the (ultimate) element type of this array type.
   * This method should only be used for an array type.
   *
   * @return Returns the type of the elements of this array type.
   *
   * can-multi-thread
   */
  def getElementType(implicit bct: BCodeTypes): BType = {
    assert(isArray, "Asked for the element type of a non-array type: " + this)
    bct.BT.getType(off + getDimensions)
  }

  /*
   * Returns the internal name of the class corresponding to this object or
   * array type. The internal name of a class is its fully qualified name (as
   * returned by Class.getName(), where '.' are replaced by '/'. This method
   * should only be used for an object or array type.
   *
   * @return the internal name of the class corresponding to this object type.
   *
   * can-multi-thread
   */
  def getInternalName(implicit bct: BCodeTypes) : String = {
    new String(bct.global.chrs, off, len)
  }

  /*
   * @return the prefix of the internal name until the last '/' (if '/' present), empty string otherwise.
   *
   * can-multi-thread
   */
  def getRuntimePackage(implicit bct: BCodeTypes) : String = {
    assert(hasObjectSort, "not of object sort: " + getDescriptor)
    val iname = getInternalName
    val idx = iname.lastIndexOf('/')
    if(idx == -1) ""
    else iname.substring(0, idx)
  }

  /*
   * @return the suffix of the internal name until the last '/' (if '/' present), internal name otherwise.
   *
   * can-multi-thread
   */
  def getSimpleName(implicit bct: BCodeTypes) : String = {
    assert(hasObjectSort, "not of object sort: " + getDescriptor)
    val iname = getInternalName
    val idx = iname.lastIndexOf('/')
    if(idx == -1) iname
    else iname.substring(idx + 1)
  }

  /*
   * Returns the argument types of methods of this type.
   * This method should only be used for method types.
   *
   * @return the argument types of methods of this type.
   *
   * can-multi-thread
   */
  def getArgumentTypes(implicit bct: BCodeTypes) : Array[BType] = {
    bct.BT.getArgumentTypes(off + 1)
  }

  /*
   * Returns the number of arguments of methods of this type.
   * This method should only be used for method types.
   *
   * @return the number of arguments of methods of this type.
   *
   * can-multi-thread
   */
  def getArgumentCount(implicit bct: BCodeTypes) : Int = {
    bct.BT.getArgumentCount(off + 1)
  }

  /*
   * Returns the return type of methods of this type.
   * This method should only be used for method types.
   *
   * @return the return type of methods of this type.
   *
   * can-multi-thread
   */
  def getReturnType(implicit bct: BCodeTypes) : BType = {
    val chrs = bct.global.chrs
    assert(chrs(off) == '(', "doesn't look like a method descriptor: " + getDescriptor)
    var resPos = off + 1
    while(chrs(resPos) != ')') { resPos += 1 }
    bct.BT.getType(resPos + 1)
  }

  /*
   *  Given a zero-based formal-param-position, return its corresponding local-var-index,
   *  taking into account the JVM-type-sizes of preceding formal params.
   */
  def convertFormalParamPosToLocalVarIdx(paramPos: Int, isInstanceMethod: Boolean)(implicit bct: BCodeTypes) : Int = {
    assert(sort == asm.Type.METHOD)
    val paramTypes = getArgumentTypes
    var local = 0
    (0 until paramPos) foreach { argPos => local += paramTypes(argPos).getSize }

    local + (if(isInstanceMethod) 1 else 0)
  }

  /*
   *  Given a local-var-index, return its corresponding zero-based formal-param-position,
   *  taking into account the JVM-type-sizes of preceding formal params.
   */
  def convertLocalVarIdxToFormalParamPos(localIdx: Int, isInstanceMethod: Boolean)(implicit bct: BCodeTypes) : Int = {
    assert(sort == asm.Type.METHOD)
    val paramTypes = getArgumentTypes
    var remaining  = (if(isInstanceMethod) (localIdx - 1) else localIdx)
    assert(remaining >= 0)
    var result     = 0
    while(remaining > 0) {
      remaining -= paramTypes(result).getSize
      result    += 1
    }
    assert(remaining == 0)

    result
  }

  // ------------------------------------------------------------------------
  // Inspector methods
  // ------------------------------------------------------------------------

  def isPrimitiveOrVoid = (sort <  asm.Type.ARRAY) // can-multi-thread
  def isValueType       = (sort <  asm.Type.ARRAY) // can-multi-thread
  def isArray           = (sort == asm.Type.ARRAY) // can-multi-thread
  def isUnitType        = (sort == asm.Type.VOID)  // can-multi-thread

  def isRefOrArrayType   = { hasObjectSort ||  isArray    } // can-multi-thread
  def isNonUnitValueType = { isValueType   && !isUnitType } // can-multi-thread

  def isNonSpecial  (implicit bct: BCodeTypes) = { !isValueType && !isArray && !isPhantomType   }         // can-multi-thread
  def isNothingType (implicit bct: BCodeTypes) = { (this == bct.RT_NOTHING) || (this == bct.CT_NOTHING) } // can-multi-thread
  def isNullType    (implicit bct: BCodeTypes) = { (this == bct.RT_NULL)    || (this == bct.CT_NULL)    } // can-multi-thread
  def isPhantomType (implicit bct: BCodeTypes) = { isNothingType || isNullType } // can-multi-thread

  /*
   * can-multi-thread
   */
  def isBoxed (implicit bct: BCodeTypes) = {
    import bct._
    this match {
      case BOXED_UNIT  | BOXED_BOOLEAN | BOXED_CHAR   |
           BOXED_BYTE  | BOXED_SHORT   | BOXED_INT    |
           BOXED_FLOAT | BOXED_LONG    | BOXED_DOUBLE
        => true
      case _
        => false
    }
  }

  /* On the JVM,
   *    BOOL, BYTE, CHAR, SHORT, and INT
   *  are like Ints for the purpose of lub calculation.
   *
   * can-multi-thread
   */
  def isIntSizedType = {
    (sort : @switch) match {
      case asm.Type.BOOLEAN | asm.Type.CHAR  |
           asm.Type.BYTE    | asm.Type.SHORT | asm.Type.INT
        => true
      case _
        => false
    }
  }

  /* On the JVM, similar to isIntSizedType except that BOOL isn't integral while LONG is.
   *
   * can-multi-thread
   */
  def isIntegralType = {
    (sort : @switch) match {
      case asm.Type.CHAR  |
           asm.Type.BYTE  | asm.Type.SHORT | asm.Type.INT |
           asm.Type.LONG
        => true
      case _
        => false
    }
  }

  /* On the JVM, FLOAT and DOUBLE.
   *
   * can-multi-thread
   */
  def isRealType = { (sort == asm.Type.FLOAT ) || (sort == asm.Type.DOUBLE) }

  def isNumericType = (isIntegralType || isRealType) // can-multi-thread

  /* Is this type a category 2 type in JVM terms? (ie, is it LONG or DOUBLE?)
   *
   * can-multi-thread
   */
  def isWideType = (getSize == 2)

  def isClosureClass(implicit bct: BCodeTypes) : Boolean = {
    val tr = bct.exemplars.get(this); (tr != null && tr.isLambda)
  }

  def isCapturedCellRef(implicit bct: BCodeTypes) : Boolean = {
    import bct._

    this == srBooleanRef || this == srByteRef  ||
    this == srCharRef    ||
    this == srIntRef     ||
    this == srLongRef    ||
    this == srFloatRef   || this == srDoubleRef
  }

  /*
   * Element vs. Component type of an array:
   * Quoting from the JVMS, Sec. 2.4 "Reference Types and Values"
   *
   *   An array type consists of a component type with a single dimension (whose
   *   length is not given by the type). The component type of an array type may itself be
   *   an array type. If, starting from any array type, one considers its component type,
   *   and then (if that is also an array type) the component type of that type, and so on,
   *   eventually one must reach a component type that is not an array type; this is called
   *   the element type of the array type. The element type of an array type is necessarily
   *   either a primitive type, or a class type, or an interface type.
   *
   */

  /* The type of items this array holds.
   *
   * can-multi-thread
   */
  def getComponentType(implicit bct: BCodeTypes) : BType = {
    assert(isArray, "Asked for the component type of a non-array type: " + this)
    bct.BT.getType(off + 1)
  }

  // ------------------------------------------------------------------------
  // Conversion to type descriptors
  // ------------------------------------------------------------------------

  /*
   * @return the descriptor corresponding to this Java type.
   *
   * can-multi-thread
   */
  def getDescriptor(implicit bct: BCodeTypes) : String = {
    val buf = new StringBuffer()
    getDescriptor(buf)
    buf.toString()
  }

  /*
   * Appends the descriptor corresponding to this Java type to the given string buffer.
   *
   * @param buf the string buffer to which the descriptor must be appended.
   *
   * can-multi-thread
   */
  def getDescriptor(buf: StringBuffer)(implicit bct: BCodeTypes) {
    if (isPrimitiveOrVoid) {
      // descriptor is in byte 3 of 'off' for primitive types (buf == null)
      buf.append(((off & 0xFF000000) >>> 24).asInstanceOf[Char])
    } else if (sort == asm.Type.OBJECT) {
      buf.append('L')
      buf.append(bct.global.chrs, off, len)
      buf.append(';')
    } else { // sort == ARRAY || sort == METHOD
      buf.append(bct.global.chrs, off, len)
    }
  }

  // ------------------------------------------------------------------------
  // Corresponding size and opcodes
  // ------------------------------------------------------------------------

  /*
   * Returns the size of values of this type.
   * This method must not be used for method types.
   *
   * @return the size of values of this type, i.e., 2 for <tt>long</tt> and
   *         <tt>double</tt>, 0 for <tt>void</tt> and 1 otherwise.
   *
   * can-multi-thread
   */
  def getSize: Int = {
    // the size is in byte 0 of 'off' for primitive types (buf == null)
    if(isPrimitiveOrVoid) (off & 0xFF) else 1
  }

  /*
   * Returns a JVM instruction opcode adapted to this Java type. This method
   * must not be used for method types.
   *
   * @param opcode a JVM instruction opcode. This opcode must be one of ILOAD,
   *        ISTORE, IALOAD, IASTORE, IADD, ISUB, IMUL, IDIV, IREM, INEG, ISHL,
   *        ISHR, IUSHR, IAND, IOR, IXOR and IRETURN.
   * @return an opcode that is similar to the given opcode, but adapted to
   *         this Java type. For example, if this type is <tt>float</tt> and
   *         <tt>opcode</tt> is IRETURN, this method returns FRETURN.
   *
   * can-multi-thread
   */
  def getOpcode(opcode: Int): Int = {
    import scala.tools.asm.Opcodes
    if (opcode == Opcodes.IALOAD || opcode == Opcodes.IASTORE) {
      // the offset for IALOAD or IASTORE is in byte 1 of 'off' for
      // primitive types (buf == null)
      opcode + (if(isPrimitiveOrVoid) (off & 0xFF00) >> 8 else 4)
    } else {
      // the offset for other instructions is in byte 2 of 'off' for
      // primitive types (buf == null)
      opcode + (if (isPrimitiveOrVoid) (off & 0xFF0000) >> 16 else 4)
    }
  }

  override def toString: String = { throw new RuntimeException("Use BType.getDescriptor instead.") }

}