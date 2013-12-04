/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala
package tools.nsc
package backend.jvm

import scala.tools.asm
import scala.annotation.switch
import scala.collection.{ immutable, mutable }

/*
 *  Immutable representations of bytecode-level types.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded
 *  @version 1.0
 *
 */
abstract class BCodeGlue extends SubComponent {

  import global._

  object BT {

    import global.chrs

    // ------------- primitive types -------------

    val VOID_TYPE    = new BType(asm.Type.VOID,    ('V' << 24) | (5 << 16) | (0 << 8) | 0, 1)
    val BOOLEAN_TYPE = new BType(asm.Type.BOOLEAN, ('Z' << 24) | (0 << 16) | (5 << 8) | 1, 1)
    val CHAR_TYPE    = new BType(asm.Type.CHAR,    ('C' << 24) | (0 << 16) | (6 << 8) | 1, 1)
    val BYTE_TYPE    = new BType(asm.Type.BYTE,    ('B' << 24) | (0 << 16) | (5 << 8) | 1, 1)
    val SHORT_TYPE   = new BType(asm.Type.SHORT,   ('S' << 24) | (0 << 16) | (7 << 8) | 1, 1)
    val INT_TYPE     = new BType(asm.Type.INT,     ('I' << 24) | (0 << 16) | (0 << 8) | 1, 1)
    val FLOAT_TYPE   = new BType(asm.Type.FLOAT,   ('F' << 24) | (2 << 16) | (2 << 8) | 1, 1)
    val LONG_TYPE    = new BType(asm.Type.LONG,    ('J' << 24) | (1 << 16) | (1 << 8) | 2, 1)
    val DOUBLE_TYPE  = new BType(asm.Type.DOUBLE,  ('D' << 24) | (3 << 16) | (3 << 8) | 2, 1)

    /*
     * Returns the Java type corresponding to the given type descriptor.
     *
     * @param off the offset of this descriptor in the chrs buffer.
     * @return the Java type corresponding to the given type descriptor.
     *
     * can-multi-thread
     */
    def getType(off: Int): BType = {
      var len = 0
      chrs(off) match {
        case 'V' => VOID_TYPE
        case 'Z' => BOOLEAN_TYPE
        case 'C' => CHAR_TYPE
        case 'B' => BYTE_TYPE
        case 'S' => SHORT_TYPE
        case 'I' => INT_TYPE
        case 'F' => FLOAT_TYPE
        case 'J' => LONG_TYPE
        case 'D' => DOUBLE_TYPE
        case '[' =>
          len = 1
          while (chrs(off + len) == '[') {
            len += 1
          }
          if (chrs(off + len) == 'L') {
            len += 1
            while (chrs(off + len) != ';') {
              len += 1
            }
          }
          getCanonical(asm.Type.ARRAY, off, len + 1)
        case 'L' =>
          len = 1
          while (chrs(off + len) != ';') {
            len += 1
          }
          getCanonical(asm.Type.OBJECT, off + 1, len - 1)
        // case '(':
        case _ =>
          abort("The intended representation for bytecode-level method-types is BMType, not BType.")
      }
    }

    private def getCanonical(sort: Int, off: Int, len: Int): BType = {
      val ca  = _root_.java.util.Arrays.copyOfRange(chrs, off, off + len)
      assert(new String(chrs, off, len) == new String(ca))  // TODO debug
      val n = global.newTypeName(ca)
      // this time we've fielded on the canonical offset.
      new BType(sort, n.start, n.length)
    }

    /* Params denote an internal name.
     *  can-multi-thread
     */
    def getObjectType(index: Int, length: Int): BType = {
      val sort = if (chrs(index) == '[') asm.Type.ARRAY else asm.Type.OBJECT;
      new BType(sort, index, length)
    }

    /*
     * @param typeDescriptor a field descriptor (for method-type descriptors, use `getMethodType()`).
     *
     * must-single-thread
     */
    def getFieldType(typeDescriptor: String): BType = {
      val n = global.newTypeName(typeDescriptor)
      getType(n.start)
    }

    /*
     * Returns the descriptor corresponding to the given argument and return types.
     *
     * @param returnType the return type of the method.
     * @param argumentTypes the argument types of the method.
     * @return the descriptor corresponding to the given argument and return types.
     *
     * can-multi-thread
     */
    def getMethodDescriptor(
        returnType: BType,
        argumentTypes: Array[BType]): String =
    {
      val buf = new StringBuffer()
      buf.append('(')
      var i = 0
      while (i < argumentTypes.length) {
        argumentTypes(i).getDescriptor(buf)
        i += 1
      }
      buf.append(')')
      returnType.getDescriptor(buf)
      buf.toString()
    }

  } // end of object BT

  /*
   * Based on ASM's Type class. Namer's chrs is used in this class for the same purposes as the `buf` char array in asm.Type.
   *
   * All methods of this classs can-multi-thread
   */
  final class BType(sort0: Int, val off: Int, len0: Int) {

    import global.chrs

    private val hiPart: Int = ((sort0 << 24) | len0)

    @inline def len:  Int = (hiPart & 0x00FFFFFF)
    @inline def sort: Int = (hiPart >> 24)

    /*
     * can-multi-thread
     */
    def toASMType: scala.tools.asm.Type = {
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
    def getDimensions: Int = {
      var i = 1
      while (chrs(off + i) == '[') {
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
    def getElementType: BType = {
      assert(isArray, s"Asked for the element type of a non-array type: $this")
      BT.getType(off + getDimensions)
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
    def getInternalName: String = {
      new String(chrs, off, len)
    }

    /*
     * @return the prefix of the internal name until the last '/' (if '/' present), empty string otherwise.
     *
     * can-multi-thread
     */
    def getRuntimePackage: String = {
      assert(hasObjectSort, s"not of object sort: $toString")
      val iname = getInternalName
      val idx = iname.lastIndexOf('/')
      if (idx == -1) ""
      else iname.substring(0, idx)
    }

    /*
     * @return the suffix of the internal name until the last '/' (if '/' present), internal name otherwise.
     *
     * can-multi-thread
     */
    def getSimpleName: String = {
      assert(hasObjectSort, s"not of object sort: $toString")
      val iname = getInternalName
      val idx = iname.lastIndexOf('/')
      if (idx == -1) iname
      else iname.substring(idx + 1)
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

    def isNonSpecial  = { !isValueType && !isArray && !isPhantomType   } // can-multi-thread
    def isNothingType = { (this == RT_NOTHING) || (this == CT_NOTHING) } // can-multi-thread
    def isNullType    = { (this == RT_NULL)    || (this == CT_NULL)    } // can-multi-thread
    def isPhantomType = { isNothingType || isNullType } // can-multi-thread

    /*
     * can-multi-thread
     */
    def isBoxed = {
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
    def isRealType = ((sort == asm.Type.FLOAT ) || (sort == asm.Type.DOUBLE))

    def isNumericType = (isIntegralType || isRealType) // can-multi-thread

    /* Is this type a category 2 type in JVM terms? (ie, is it LONG or DOUBLE?)
     *
     * can-multi-thread
     */
    def isWideType = (getSize == 2)

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
    def getComponentType: BType = {
      assert(isArray, s"Asked for the component type of a non-array type: $this")
      BT.getType(off + 1)
    }

    // ------------------------------------------------------------------------
    // Conversion to type descriptors
    // ------------------------------------------------------------------------

    /*
     * @return the descriptor corresponding to this Java type.
     *
     * can-multi-thread
     */
    def getDescriptor: String = {
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
    def getDescriptor(buf: StringBuffer) {
      if (isPrimitiveOrVoid) {
        // descriptor is in byte 3 of 'off' for primitive types (buf == null)
        buf.append(((off & 0xFF000000) >>> 24).asInstanceOf[Char])
      } else if (sort == asm.Type.OBJECT) {
        buf.append('L')
        buf.append(chrs, off, len)
        buf.append(';')
      } else { // sort == ARRAY || sort == METHOD
        buf.append(chrs, off, len)
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
      if (isPrimitiveOrVoid) (off & 0xFF) else 1
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
        opcode + (if (isPrimitiveOrVoid) (off & 0xFF00) >> 8 else 4)
      } else {
        // the offset for other instructions is in byte 2 of 'off' for
        // primitive types (buf == null)
        opcode + (if (isPrimitiveOrVoid) (off & 0xFF0000) >> 16 else 4)
      }
    }

    // ------------------------------------------------------------------------
    // Equals, hashCode and toString
    // ------------------------------------------------------------------------

    /*
     * Tests if the given object is equal to this type.
     *
     * @param o the object to be compared to this type.
     * @return <tt>true</tt> if the given object is equal to this type.
     *
     * can-multi-thread
     */
    override def equals(o: Any): Boolean = {
      if (!(o.isInstanceOf[BType])) {
        return false
      }
      val t = o.asInstanceOf[BType]
      (hiPart == t.hiPart) && (off == t.off)
    }

    /*
     * @return a hash code value for this type.
     *
     * can-multi-thread
     */
    override def hashCode(): Int = {
      13 * hiPart + 17 * off
    }

    /*
     * @return the descriptor of this type.
     *
     * can-multi-thread
     */
    override def toString: String = { getDescriptor }

  }

  /*
   * Creates a TypeName and the BType token for it.
   * This method does not add to `innerClassBufferASM`, use `internalName()` or `asmType()` or `toTypeKind()` for that.
   *
   * must-single-thread
   */
  def brefType(iname: String): BType = { brefType(newTypeName(iname.toCharArray(), 0, iname.length())) }

  /*
   * Creates a BType token for the TypeName received as argument.
   * This method does not add to `innerClassBufferASM`, use `internalName()` or `asmType()` or `toTypeKind()` for that.
   *
   *  can-multi-thread
   */
  def brefType(iname: TypeName): BType = BT.getObjectType(iname.start, iname.length)

  // due to keyboard economy only
  val UNIT   = BT.VOID_TYPE
  val BOOL   = BT.BOOLEAN_TYPE
  val CHAR   = BT.CHAR_TYPE
  val BYTE   = BT.BYTE_TYPE
  val SHORT  = BT.SHORT_TYPE
  val INT    = BT.INT_TYPE
  val LONG   = BT.LONG_TYPE
  val FLOAT  = BT.FLOAT_TYPE
  val DOUBLE = BT.DOUBLE_TYPE

  val BOXED_UNIT    = brefType("java/lang/Void")
  val BOXED_BOOLEAN = brefType("java/lang/Boolean")
  val BOXED_BYTE    = brefType("java/lang/Byte")
  val BOXED_SHORT   = brefType("java/lang/Short")
  val BOXED_CHAR    = brefType("java/lang/Character")
  val BOXED_INT     = brefType("java/lang/Integer")
  val BOXED_LONG    = brefType("java/lang/Long")
  val BOXED_FLOAT   = brefType("java/lang/Float")
  val BOXED_DOUBLE  = brefType("java/lang/Double")

  /*
   * RT_NOTHING and RT_NULL exist at run-time only.
   * They are the bytecode-level manifestation (in method signatures only) of what shows up as NothingClass resp. NullClass in Scala ASTs.
   * Therefore, when RT_NOTHING or RT_NULL are to be emitted,
   * a mapping is needed: the internal names of NothingClass and NullClass can't be emitted as-is.
   */
  val RT_NOTHING = brefType("scala/runtime/Nothing$")
  val RT_NULL    = brefType("scala/runtime/Null$")
  val CT_NOTHING = brefType("scala/Nothing") // TODO needed?
  val CT_NULL    = brefType("scala/Null")    // TODO needed?

  val srBooleanRef = brefType("scala/runtime/BooleanRef")
  val srByteRef    = brefType("scala/runtime/ByteRef")
  val srCharRef    = brefType("scala/runtime/CharRef")
  val srIntRef     = brefType("scala/runtime/IntRef")
  val srLongRef    = brefType("scala/runtime/LongRef")
  val srFloatRef   = brefType("scala/runtime/FloatRef")
  val srDoubleRef  = brefType("scala/runtime/DoubleRef")

  /*  Map from type kinds to the Java reference types.
   *  Useful when pushing class literals onto the operand stack (ldc instruction taking a class literal).
   *  @see Predef.classOf
   *  @see genConstant()
   */
  val classLiteral = immutable.Map[BType, BType](
    UNIT   -> BOXED_UNIT,
    BOOL   -> BOXED_BOOLEAN,
    BYTE   -> BOXED_BYTE,
    SHORT  -> BOXED_SHORT,
    CHAR   -> BOXED_CHAR,
    INT    -> BOXED_INT,
    LONG   -> BOXED_LONG,
    FLOAT  -> BOXED_FLOAT,
    DOUBLE -> BOXED_DOUBLE
  )

  case class MethodNameAndType(mname: String, mdesc: String)

  val asmBoxTo: Map[BType, MethodNameAndType] = {
    Map(
      BOOL   -> MethodNameAndType("boxToBoolean",   "(Z)Ljava/lang/Boolean;"  ) ,
      BYTE   -> MethodNameAndType("boxToByte",      "(B)Ljava/lang/Byte;"     ) ,
      CHAR   -> MethodNameAndType("boxToCharacter", "(C)Ljava/lang/Character;") ,
      SHORT  -> MethodNameAndType("boxToShort",     "(S)Ljava/lang/Short;"    ) ,
      INT    -> MethodNameAndType("boxToInteger",   "(I)Ljava/lang/Integer;"  ) ,
      LONG   -> MethodNameAndType("boxToLong",      "(J)Ljava/lang/Long;"     ) ,
      FLOAT  -> MethodNameAndType("boxToFloat",     "(F)Ljava/lang/Float;"    ) ,
      DOUBLE -> MethodNameAndType("boxToDouble",    "(D)Ljava/lang/Double;"   )
    )
  }

  val asmUnboxTo: Map[BType, MethodNameAndType] = {
    Map(
      BOOL   -> MethodNameAndType("unboxToBoolean", "(Ljava/lang/Object;)Z") ,
      BYTE   -> MethodNameAndType("unboxToByte",    "(Ljava/lang/Object;)B") ,
      CHAR   -> MethodNameAndType("unboxToChar",    "(Ljava/lang/Object;)C") ,
      SHORT  -> MethodNameAndType("unboxToShort",   "(Ljava/lang/Object;)S") ,
      INT    -> MethodNameAndType("unboxToInt",     "(Ljava/lang/Object;)I") ,
      LONG   -> MethodNameAndType("unboxToLong",    "(Ljava/lang/Object;)J") ,
      FLOAT  -> MethodNameAndType("unboxToFloat",   "(Ljava/lang/Object;)F") ,
      DOUBLE -> MethodNameAndType("unboxToDouble",  "(Ljava/lang/Object;)D")
    )
  }

  /*
   *  can-multi-thread
   */
  def toBType(t: asm.Type): BType = {
    (t.getSort: @switch) match {
      case asm.Type.VOID    => BT.VOID_TYPE
      case asm.Type.BOOLEAN => BT.BOOLEAN_TYPE
      case asm.Type.CHAR    => BT.CHAR_TYPE
      case asm.Type.BYTE    => BT.BYTE_TYPE
      case asm.Type.SHORT   => BT.SHORT_TYPE
      case asm.Type.INT     => BT.INT_TYPE
      case asm.Type.FLOAT   => BT.FLOAT_TYPE
      case asm.Type.LONG    => BT.LONG_TYPE
      case asm.Type.DOUBLE  => BT.DOUBLE_TYPE

      case asm.Type.ARRAY   |
           asm.Type.OBJECT  =>
        // TODO confirm whether this also takes care of the phantom types.
        val key = t.getInternalName
        val bt  = lookupRefBTypeIfExisting(key)
        if (bt == null) brefType(key)
        else bt

      case asm.Type.METHOD  =>
        abort("The intended representation for bytecode-level method-types is BMType, not BType.")
    }
  }

  def toBType(ts: Array[asm.Type]): Array[BType] = ts map toBType

  /*
   * ASM trees represent types as strings (internal names, descriptors).
   * Given that we operate instead on BTypes, conversion is needed when visiting MethodNodes outside GenBCode.
   *
   * can-multi-thread
   */
  def descrToBType(typeDescriptor: String): BType = {
    val c: Char = typeDescriptor(0)
    c match {
      case 'V' => BT.VOID_TYPE
      case 'Z' => BT.BOOLEAN_TYPE
      case 'C' => BT.CHAR_TYPE
      case 'B' => BT.BYTE_TYPE
      case 'S' => BT.SHORT_TYPE
      case 'I' => BT.INT_TYPE
      case 'F' => BT.FLOAT_TYPE
      case 'J' => BT.LONG_TYPE
      case 'D' => BT.DOUBLE_TYPE
      case 'L' =>
        val iname = typeDescriptor.substring(1, typeDescriptor.length() - 1)
        val n = global.lookupTypeName(iname.toCharArray)
        new BType(asm.Type.OBJECT, n.start, n.length)
      case _   =>
        val n = global.lookupTypeName(typeDescriptor.toCharArray)
        BT.getType(n.start)
    }
  }

  /*
   * Use only to lookup reference types, otherwise use `descrToBType()`
   *
   * can-multi-thread
   */
  def lookupRefBType(iname: String): BType = {
    import global.chrs
    val n    = global.lookupTypeName(iname.toCharArray)
    val sort = if (chrs(n.start) == '[') asm.Type.ARRAY else asm.Type.OBJECT;
    new BType(sort, n.start, n.length)
  }

  def lookupRefBTypeIfExisting(iname: String): BType = {
    import global.chrs
    val n    = global.lookupTypeNameIfExisting(iname.toCharArray, false)
    if (n == null) { return null }
    val sort = if (chrs(n.start) == '[') asm.Type.ARRAY else asm.Type.OBJECT;
    new BType(sort, n.start, n.length)
  }

  /*
   * Bytecode-level Method types support sufficiently different operations,
   * and moreover are usually discarded shortly after instantiation.
   * Rather than having them compete for cache space in the chrs array
   * with (logner-lived) BTypes, this class is dedicated to represent them.
   */
  case class BMType(returnType: BType, argumentTypes: Array[BType]) {

    /*
     * Returns the number of arguments of methods of this type.
     * This method should only be used for method types.
     *
     * @return the number of arguments of methods of this type.
     *
     * can-multi-thread
     */
    def getArgumentCount: Int = { argumentTypes.length }

    def getDescriptor: String = { BT.getMethodDescriptor(returnType, argumentTypes) }

    /*
     *  Given a zero-based formal-param-position, return its corresponding local-var-index,
     *  taking into account the JVM-type-sizes of preceding formal params.
     */
    def convertFormalParamPosToLocalVarIdx(paramPos: Int, isInstanceMethod: Boolean): Int = {
      var local = 0
      (0 until paramPos) foreach { argPos => local += argumentTypes(argPos).getSize }

      local + (if (isInstanceMethod) 1 else 0)
    }

    /*
     *  Given a local-var-index, return its corresponding zero-based formal-param-position,
     *  taking into account the JVM-type-sizes of preceding formal params.
     */
    def convertLocalVarIdxToFormalParamPos(localIdx: Int, isInstanceMethod: Boolean): Int = {
      var remaining  = (if (isInstanceMethod) (localIdx - 1) else localIdx)
      assert(remaining >= 0)
      var result     = 0
      while (remaining > 0) {
        remaining -= argumentTypes(result).getSize
        result    += 1
      }
      assert(remaining == 0)

      result
    }

  }

  object BMType {

    def apply(methodDescriptor: String): BMType = {
      val t = asm.Type.getMethodType(methodDescriptor)
      apply(t)
    }

    def apply(at: asm.Type): BMType = {
      val r  = toBType(at.getReturnType)
      val as = toBType(at.getArgumentTypes)
      apply(r, as)
    }

  }

}
