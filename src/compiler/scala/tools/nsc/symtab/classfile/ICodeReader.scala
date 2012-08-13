/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author Iulian Dragos
 */

package scala.tools.nsc
package symtab
package classfile

import scala.collection.{ mutable, immutable }
import mutable.ListBuffer
import backend.icode._
import ClassfileConstants._
import scala.reflect.internal.Flags._

/** ICode reader from Java bytecode.
 *
 *  @author Iulian Dragos
 *  @version 1.0
 */
abstract class ICodeReader extends ClassfileParser {
  val global: Global
  import global._
  import icodes._

  var instanceCode: IClass = null          // the ICode class for the current symbol
  var staticCode:   IClass = null          // the ICode class static members
  var method: IMethod = NoIMethod          // the current IMethod
  var isScalaModule = false

  /** Read back bytecode for the given class symbol. It returns
   *  two IClass objects, one for static members and one
   *  for non-static members.
   */
  def readClass(cls: Symbol): (IClass, IClass) = {
    var classFile: io.AbstractFile = null;
    cls.info // ensure accurate type information

    isScalaModule = cls.isModule && !cls.isJavaDefined
    log("Reading class: " + cls + " isScalaModule?: " + isScalaModule)
    val name = cls.javaClassName

    classPath.findSourceFile(name) match {
      case Some(classFile) => parse(classFile, cls)
      case _               => MissingRequirementError.notFound("Could not find bytecode for " + cls)
    }

    (staticCode, instanceCode)
  }

  /** If we're parsing a scala module, the owner of members is always
   *  the module symbol.
   */
  override def getOwner(jflags: Int): Symbol =
    if (isScalaModule) this.staticModule
    else super.getOwner(jflags)

  override def parseClass() {
    this.instanceCode = new IClass(clazz)
    this.staticCode   = new IClass(staticModule)
    val jflags = in.nextChar
    val isAttribute = (jflags & JAVA_ACC_ANNOTATION) != 0
    val sflags = toScalaClassFlags(jflags)  // what, this is never used??
    val c = pool getClassSymbol in.nextChar

    parseInnerClasses()

    in.skip(2)               // super class
    in.skip(2 * in.nextChar) // interfaces
    val fieldCount = in.nextChar
    for (i <- 0 until fieldCount) parseField()
    val methodCount = in.nextChar
    for (i <- 0 until methodCount) parseMethod();
    instanceCode.methods = instanceCode.methods.reverse
    staticCode.methods = staticCode.methods.reverse
  }

  override def parseField() {
    val (jflags, sym) = parseMember(true)
    getCode(jflags) addField new IField(sym)
    skipAttributes()
  }

  private def parseMember(field: Boolean): (Int, Symbol) = {
    val jflags   = in.nextChar
    val name     = pool getName in.nextChar
    val owner    = getOwner(jflags)
    val dummySym = owner.newMethod(name, owner.pos, toScalaMethodFlags(jflags))

    try {
      val ch  = in.nextChar
      val tpe = pool.getType(dummySym, ch)

      if ("<clinit>" == name.toString)
        (jflags, NoSymbol)
      else {
        val owner = getOwner(jflags)
        var sym = owner.info.findMember(name, 0, 0, false).suchThat(old => sameType(old.tpe, tpe))
        if (sym == NoSymbol)
          sym = owner.info.findMember(newTermName(name + nme.LOCAL_SUFFIX_STRING), 0, 0, false).suchThat(_.tpe =:= tpe)
        if (sym == NoSymbol) {
          log("Could not find symbol for " + name + ": " + tpe)
          log(owner.info.member(name).tpe + " : " + tpe)
          sym = if (field) owner.newValue(name, owner.pos, toScalaFieldFlags(jflags)) else dummySym
          sym setInfoAndEnter tpe
          log("added " + sym + ": " + sym.tpe)
        }
        (jflags, sym)
      }
    } catch {
      case e: MissingRequirementError =>
        (jflags, NoSymbol)
    }
  }

  /** Checks if `tp1` is the same type as `tp2`, modulo implicit methods.
   *  We don't care about the distinction between implicit and explicit
   *  methods as this point, and we can't get back the information from
   *  bytecode anyway.
   */
  private def sameType(tp1: Type, tp2: Type): Boolean = (tp1, tp2) match {
    case (mt1 @ MethodType(args1, resTpe1), mt2 @ MethodType(args2, resTpe2)) if mt1.isImplicit || mt2.isImplicit =>
      MethodType(args1, resTpe1) =:= MethodType(args2, resTpe2)
    case _ =>
      tp1 =:= tp2
  }

  override def parseMethod() {
    val (jflags, sym) = parseMember(false)
    var beginning = in.bp
    try {
      if (sym != NoSymbol) {
        this.method = new IMethod(sym)
        this.method.returnType = toTypeKind(sym.tpe.resultType)
        getCode(jflags).addMethod(this.method)
        if ((jflags & JAVA_ACC_NATIVE) != 0)
          this.method.native = true
        val attributeCount = in.nextChar
        for (i <- 0 until attributeCount) parseAttribute()
      } else {
        debuglog("Skipping non-existent method.");
        skipAttributes();
      }
    } catch {
      case e: MissingRequirementError =>
        in.bp = beginning; skipAttributes
        debuglog("Skipping non-existent method. " + e.msg);
    }
  }

  def parseAttribute() {
    val attrName = pool.getName(in.nextChar).toTypeName
    val attrLen = in.nextInt
    attrName match {
      case tpnme.CodeATTR =>
        parseByteCode()
      case _ =>
        in.skip(attrLen)
    }
  }

  override def classNameToSymbol(name: Name) = {
    val sym = if (name == fulltpnme.RuntimeNothing)
      definitions.NothingClass
    else if (name == fulltpnme.RuntimeNull)
      definitions.NullClass
    else if (nme.isImplClassName(name)) {
      val iface = rootMirror.getClassByName(tpnme.interfaceName(name))
      log("forcing " + iface.owner + " at phase: " + phase + " impl: " + iface.implClass)
      iface.owner.info // force the mixin type-transformer
      rootMirror.getClassByName(name)
    }
    else if (nme.isModuleName(name)) {
      val strippedName = nme.stripModuleSuffix(name)
      val sym = forceMangledName(newTermName(strippedName.decode), true)

      if (sym == NoSymbol) rootMirror.getModule(strippedName)
      else sym
    }
    else {
      forceMangledName(name, false)
      afterFlatten(rootMirror.getClassByName(name.toTypeName))
    }
    if (sym.isModule)
      sym.moduleClass
    else
      sym
  }


  var maxStack: Int = _
  var maxLocals: Int = _
  val JVM = ClassfileConstants // shorter, uppercase alias for use in case patterns

  def toUnsignedByte(b: Byte): Int = b.toInt & 0xff
  var pc = 0

  /** Parse java bytecode into ICode */
  def parseByteCode() {
    maxStack = in.nextChar
    maxLocals = in.nextChar
    val codeLength = in.nextInt
    val code = new LinearCode

    def parseInstruction() {
      import opcodes._
      import code._
      var size = 1 // instruction size

      /** Parse 16 bit jump target. */
      def parseJumpTarget = {
        size += 2
        val offset = in.nextChar.toShort
        val target = pc + offset
        assert(target >= 0 && target < codeLength, "Illegal jump target: " + target)
        target
      }

      /** Parse 32 bit jump target. */
      def parseJumpTargetW: Int = {
        size += 4
        val offset = in.nextInt
        val target = pc + offset
        assert(target >= 0 && target < codeLength, "Illegal jump target: " + target + "pc: " + pc + " offset: " + offset)
        target
      }

      def const(c: Constant) { code emit CONSTANT(c) }

      def loadArrayItem (tk: TypeKind) { code emit LOAD_ARRAY_ITEM(tk)  }
      def storeArrayItem(tk: TypeKind) { code emit STORE_ARRAY_ITEM(tk) }

      def loadLocal(idx: Int, tk: TypeKind) {
        val local = code.getLocal(idx, tk);
        code emit LOAD_LOCAL(local)
      }
      def storeLocal(idx: Int, tk: TypeKind) {
        val local = code.getLocal(idx, tk);
        code emit STORE_LOCAL(local)
      }
      def arith  (op: ArithmeticOp, tk:  TypeKind) { code.emit(CALL_PRIMITIVE(Arithmetic(op,  tk)))  }
      def shift  (op: ShiftOp,      tk:  TypeKind) { code.emit(CALL_PRIMITIVE(Shift     (op,  tk)))  }
      def logical(op: LogicalOp,    tk:  TypeKind) { code.emit(CALL_PRIMITIVE(Logical   (op,  tk)))  }
      def conv   (src: TypeKind,    dst: TypeKind) { code.emit(CALL_PRIMITIVE(Conversion(src, dst))) }
      def comp   (op: ComparisonOp, tk: TypeKind)  { code.emit(CALL_PRIMITIVE(Comparison(op,  tk)))  }
      def ngt(tk: TypeKind) { code.emit(CALL_PRIMITIVE(Negation(tk))) }

      val instr = toUnsignedByte(in.nextByte)
      (instr: @scala.annotation.switch) match {
        case JVM.nop => parseInstruction
        case JVM.aconst_null => const(Constant(null))
        case JVM.iconst_m1   => const(Constant(-1)  )
        case JVM.iconst_0 | JVM.iconst_1 | JVM.iconst_2 | JVM.iconst_3 | JVM.iconst_4 | JVM.iconst_5 =>
          val i: Int = (instr.toInt - JVM.iconst_0) // just to make expiclit we want Constant(Int)
          const(Constant(i))

        case JVM.lconst_0    => const(Constant(0l)  )
        case JVM.lconst_1    => const(Constant(1l)  )
        case JVM.fconst_0    => const(Constant(0.0f))
        case JVM.fconst_1    => const(Constant(1.0f))
        case JVM.fconst_2    => const(Constant(2.0f))
        case JVM.dconst_0    => const(Constant(0.0) )
        case JVM.dconst_1    => const(Constant(1.0) )

        case JVM.bipush      => const(Constant(in.nextByte)); size += 1
        case JVM.sipush      =>
          /* Quoting from the JVMS, sipush instruction:
           *   The immediate unsigned byte1 and byte2 values are assembled into an
           *   intermediate short where the value of the short is (byte1 << 8) | byte2.
           *   The intermediate value is then sign-extended to an int value. That value
           *   is pushed onto the operand stack.
           *
           * Why this works? See http://stackoverflow.com/questions/736815/2-bytes-to-short-java
           **/
          const(Constant(in.nextChar)); size += 2
        case JVM.ldc         => const (pool.getConstant(toUnsignedByte(in.nextByte))); size += 1
        case JVM.ldc_w       => const (pool.getConstant(in.nextChar)); size += 2
        case JVM.ldc2_w      => const (pool.getConstant(in.nextChar)); size += 2
        case JVM.iload       => loadLocal (in.nextByte, INT   ); size += 1
        case JVM.lload       => loadLocal (in.nextByte, LONG  ); size += 1
        case JVM.fload       => loadLocal (in.nextByte, FLOAT ); size += 1
        case JVM.dload       => loadLocal (in.nextByte, DOUBLE); size += 1
        case JVM.aload       =>
          val local = in.nextByte.toInt; size += 1
          if (local == 0 && !method.isStatic)
            code.emit(THIS(method.symbol.owner));
          else
            loadLocal (local, ObjectReference);

        case JVM.iload_0 | JVM.iload_1 | JVM.iload_2 | JVM.iload_3 => loadLocal ((instr.toInt - JVM.iload_0), INT   )
        case JVM.lload_0 | JVM.lload_1 | JVM.lload_2 | JVM.lload_3 => loadLocal ((instr.toInt - JVM.lload_0), LONG  )
        case JVM.fload_0 | JVM.fload_1 | JVM.fload_2 | JVM.fload_3 => loadLocal ((instr.toInt - JVM.fload_0), FLOAT )
        case JVM.dload_0 | JVM.dload_1 | JVM.dload_2 | JVM.dload_3 => loadLocal ((instr.toInt - JVM.dload_0), DOUBLE)

        case JVM.aload_0     =>
          if (!method.isStatic) code.emit(THIS(method.symbol.owner))
          else                  loadLocal (0, ObjectReference);
        case JVM.aload_1     => loadLocal (1, ObjectReference)
        case JVM.aload_2     => loadLocal (2, ObjectReference)
        case JVM.aload_3     => loadLocal (3, ObjectReference)

        case JVM.iaload      => loadArrayItem(INT)
        case JVM.laload      => loadArrayItem(LONG)
        case JVM.faload      => loadArrayItem(FLOAT)
        case JVM.daload      => loadArrayItem(DOUBLE)
        case JVM.aaload      => loadArrayItem(ObjectReference)
        case JVM.baload      => loadArrayItem(BYTE)
        case JVM.caload      => loadArrayItem(CHAR)
        case JVM.saload      => loadArrayItem(SHORT)

        case JVM.istore      => storeLocal (in.nextByte, INT   ); size += 1
        case JVM.lstore      => storeLocal (in.nextByte, LONG  ); size += 1
        case JVM.fstore      => storeLocal (in.nextByte, FLOAT ); size += 1
        case JVM.dstore      => storeLocal (in.nextByte, DOUBLE); size += 1
        case JVM.astore      => storeLocal (in.nextByte, ObjectReference); size += 1

        case JVM.istore_0 | JVM.istore_1 | JVM.istore_2 | JVM.istore_3 => storeLocal ((instr.toInt - JVM.istore_0), INT   )
        case JVM.lstore_0 | JVM.lstore_1 | JVM.lstore_2 | JVM.lstore_3 => storeLocal ((instr.toInt - JVM.lstore_0), LONG  )
        case JVM.fstore_0 | JVM.fstore_1 | JVM.fstore_2 | JVM.fstore_3 => storeLocal ((instr.toInt - JVM.fstore_0), FLOAT )
        case JVM.dstore_0 | JVM.dstore_1 | JVM.dstore_2 | JVM.dstore_3 => storeLocal ((instr.toInt - JVM.dstore_0), DOUBLE)

        case JVM.astore_0    =>
          if (!method.isStatic) code.emit(STORE_THIS(ObjectReference))
          else                  storeLocal (0, ObjectReference)
        case JVM.astore_1    => storeLocal (1, ObjectReference)
        case JVM.astore_2    => storeLocal (2, ObjectReference)
        case JVM.astore_3    => storeLocal (3, ObjectReference)

        case JVM.iastore     => storeArrayItem(INT)
        case JVM.lastore     => storeArrayItem(LONG)
        case JVM.fastore     => storeArrayItem(FLOAT)
        case JVM.dastore     => storeArrayItem(DOUBLE)
        case JVM.aastore     => storeArrayItem(ObjectReference)
        case JVM.bastore     => storeArrayItem(BYTE)
        case JVM.castore     => storeArrayItem(CHAR)
        case JVM.sastore     => storeArrayItem(SHORT)

        case JVM.pop         => code.emit(DROP(INT))   // any 1-word type would do

        /* TODO the only way to emit the correct TypeKind (LONG or DOUBLE, below)
         * involves fixing things up similar to what resolveDups() does. */
        case JVM.pop2        => code.emit(DROP(LONG))  // any 2-word type would do

        case JVM.dup         => code.emit(DUP(ObjectReference)) // TODO: Is the kind inside DUP ever needed?
        case JVM.dup_x1      => code.emit(DUP_X1)      // sys.error("Unsupported JVM bytecode: dup_x1")
        case JVM.dup_x2      => code.emit(DUP_X2)      // sys.error("Unsupported JVM bytecode: dup_x2")
        case JVM.dup2        => code.emit(DUP(LONG))   // TODO: Is the kind inside DUP ever needed?
        case JVM.dup2_x1     => code.emit(DUP2_X1)     // sys.error("Unsupported JVM bytecode: dup2_x1")
        case JVM.dup2_x2     => code.emit(DUP2_X2)     // sys.error("Unsupported JVM bytecode: dup2_x2")
        case JVM.swap        => sys.error("Unsupported JVM bytecode: swap")

        case JVM.iadd        => arith(ADD, INT   )
        case JVM.ladd        => arith(ADD, LONG  )
        case JVM.fadd        => arith(ADD, FLOAT )
        case JVM.dadd        => arith(ADD, DOUBLE)
        case JVM.isub        => arith(SUB, INT   )
        case JVM.lsub        => arith(SUB, LONG  )
        case JVM.fsub        => arith(SUB, FLOAT )
        case JVM.dsub        => arith(SUB, DOUBLE)
        case JVM.imul        => arith(MUL, INT   )
        case JVM.lmul        => arith(MUL, LONG  )
        case JVM.fmul        => arith(MUL, FLOAT )
        case JVM.dmul        => arith(MUL, DOUBLE)
        case JVM.idiv        => arith(DIV, INT   )
        case JVM.ldiv        => arith(DIV, LONG  )
        case JVM.fdiv        => arith(DIV, FLOAT )
        case JVM.ddiv        => arith(DIV, DOUBLE)
        case JVM.irem        => arith(REM, INT   )
        case JVM.lrem        => arith(REM, LONG  )
        case JVM.frem        => arith(REM, FLOAT )
        case JVM.drem        => arith(REM, DOUBLE)

        case JVM.ineg        => ngt(INT   )
        case JVM.lneg        => ngt(LONG  )
        case JVM.fneg        => ngt(FLOAT )
        case JVM.dneg        => ngt(DOUBLE)

        case JVM.ishl        => shift   (LSL, INT )
        case JVM.lshl        => shift   (LSL, LONG)
        case JVM.ishr        => shift   (LSR, INT )
        case JVM.lshr        => shift   (LSR, LONG)
        case JVM.iushr       => shift   (ASR, INT )
        case JVM.lushr       => shift   (ASR, LONG)

        case JVM.iand        => logical (AND, INT)
        case JVM.land        => logical (AND, LONG)
        case JVM.ior         => logical (OR,  INT )
        case JVM.lor         => logical (OR,  LONG)
        case JVM.ixor        => logical (XOR, INT )
        case JVM.lxor        => logical (XOR, LONG)
        case JVM.iinc        =>
          size += 2
          val local = code.getLocal(in.nextByte, INT)
          code.emit(LOAD_LOCAL(local))
          code.emit(CONSTANT(Constant(in.nextByte)))
          code.emit(CALL_PRIMITIVE(Arithmetic(ADD, INT)))
          code.emit(STORE_LOCAL(local))

        case JVM.i2l         => conv (INT,    LONG  )
        case JVM.i2f         => conv (INT,    FLOAT )
        case JVM.i2d         => conv (INT,    DOUBLE)
        case JVM.l2i         => conv (LONG,   INT   )
        case JVM.l2f         => conv (LONG,   FLOAT )
        case JVM.l2d         => conv (LONG,   DOUBLE)
        case JVM.f2i         => conv (FLOAT,  INT   )
        case JVM.f2l         => conv (FLOAT,  LONG  )
        case JVM.f2d         => conv (FLOAT,  DOUBLE)
        case JVM.d2i         => conv (DOUBLE, INT   )
        case JVM.d2l         => conv (DOUBLE, LONG  )
        case JVM.d2f         => conv (DOUBLE, FLOAT )
        case JVM.i2b         => conv (INT,    BYTE  )
        case JVM.i2c         => conv (INT,    CHAR  )
        case JVM.i2s         => conv (INT,    SHORT )

        case JVM.lcmp        => comp (CMP,    LONG  )
        case JVM.fcmpl       => comp (CMPL,   FLOAT )
        case JVM.fcmpg       => comp (CMPG,   FLOAT )
        case JVM.dcmpl       => comp (CMPL,   DOUBLE)
        case JVM.dcmpg       => comp (CMPG,   DOUBLE)

        case JVM.ifeq        => code.emit(LCZJUMP(parseJumpTarget, pc + size, EQ, INT))
        case JVM.ifne        => code.emit(LCZJUMP(parseJumpTarget, pc + size, NE, INT))
        case JVM.iflt        => code.emit(LCZJUMP(parseJumpTarget, pc + size, LT, INT))
        case JVM.ifge        => code.emit(LCZJUMP(parseJumpTarget, pc + size, GE, INT))
        case JVM.ifgt        => code.emit(LCZJUMP(parseJumpTarget, pc + size, GT, INT))
        case JVM.ifle        => code.emit(LCZJUMP(parseJumpTarget, pc + size, LE, INT))

        case JVM.if_icmpeq   => code.emit(LCJUMP(parseJumpTarget, pc + size, EQ, INT))
        case JVM.if_icmpne   => code.emit(LCJUMP(parseJumpTarget, pc + size, NE, INT))
        case JVM.if_icmplt   => code.emit(LCJUMP(parseJumpTarget, pc + size, LT, INT))
        case JVM.if_icmpge   => code.emit(LCJUMP(parseJumpTarget, pc + size, GE, INT))
        case JVM.if_icmpgt   => code.emit(LCJUMP(parseJumpTarget, pc + size, GT, INT))
        case JVM.if_icmple   => code.emit(LCJUMP(parseJumpTarget, pc + size, LE, INT))
        case JVM.if_acmpeq   => code.emit(LCJUMP(parseJumpTarget, pc + size, EQ, ObjectReference))
        case JVM.if_acmpne   => code.emit(LCJUMP(parseJumpTarget, pc + size, NE, ObjectReference))

        case JVM.goto        => emit(LJUMP(parseJumpTarget))
        case JVM.jsr         => sys.error("Cannot handle jsr/ret")
        case JVM.ret         => sys.error("Cannot handle jsr/ret")
        case JVM.tableswitch =>
          val padding = if ((pc + size) % 4 != 0) 4 - ((pc + size) % 4) else 0
          size += padding
          in.bp += padding
          assert((pc + size % 4) != 0, pc)
/*          var byte1 = in.nextByte; size += 1;
          while (byte1 == 0) { byte1 = in.nextByte; size += 1; }
          val default = byte1 << 24 | in.nextByte << 16 | in.nextByte << 8 | in.nextByte;
          size = size + 3
       */
          val default = pc + in.nextInt; size += 4
          val low  = in.nextInt
          val high = in.nextInt
          size += 8
          assert(low <= high, "Value low not <= high for tableswitch.")

          val tags = List.tabulate(high - low + 1)(n => List(low + n))
          val targets = for (_ <- tags) yield parseJumpTargetW
          code.emit(LSWITCH(tags, targets ::: List(default)))

        case JVM.lookupswitch =>
          val padding = if ((pc + size) % 4 != 0) 4 - ((pc + size) % 4) else 0
          size += padding
          in.bp += padding
          assert((pc + size % 4) != 0, pc)
          val default = pc + in.nextInt; size += 4
          val npairs = in.nextInt; size += 4
          var tags: List[List[Int]] = Nil
          var targets: List[Int] = Nil
          var i = 0
          while (i < npairs) {
            tags = List(in.nextInt) :: tags; size += 4
            targets = parseJumpTargetW :: targets; // parseJumpTargetW updates 'size' itself
            i += 1
          }
          targets = default :: targets
          code.emit(LSWITCH(tags.reverse, targets.reverse))

        case JVM.ireturn     => code.emit(RETURN(INT))
        case JVM.lreturn     => code.emit(RETURN(LONG))
        case JVM.freturn     => code.emit(RETURN(FLOAT))
        case JVM.dreturn     => code.emit(RETURN(DOUBLE))
        case JVM.areturn     => code.emit(RETURN(ObjectReference))
        case JVM.return_     => code.emit(RETURN(UNIT))

        case JVM.getstatic    =>
          val field = pool.getMemberSymbol(in.nextChar, true); size += 2
          if (field.hasModuleFlag)
            code emit LOAD_MODULE(field)
          else {
            assert(field.name != nme.MODULE_INSTANCE_FIELD,
                   "Loading modules has to be represented as LOAD_MODULE otherwise we'll get VerifiyError afterwards.")
            code emit LOAD_FIELD(field, true)
          }
        case JVM.putstatic   =>
          val field = pool.getMemberSymbol(in.nextChar, true); size += 2
          code.emit(STORE_FIELD(field, true))
        case JVM.getfield    =>
          val field = pool.getMemberSymbol(in.nextChar, false); size += 2
          code.emit(LOAD_FIELD(field, false))
        case JVM.putfield    =>
          val field = pool.getMemberSymbol(in.nextChar, false); size += 2
          code.emit(STORE_FIELD(field, false))

        case JVM.invokevirtual =>
          val m = pool.getMemberSymbol(in.nextChar, false); size += 2
          code.emit(CALL_METHOD(m, Dynamic))
        case JVM.invokeinterface  =>
          val m = pool.getMemberSymbol(in.nextChar, false); size += 4
          in.skip(2)
          code.emit(CALL_METHOD(m, Dynamic))
        case JVM.invokespecial   =>
          val m = pool.getMemberSymbol(in.nextChar, false); size += 2
          val style = if (m.name == nme.CONSTRUCTOR || m.isPrivate) Static(true)
                      else SuperCall(m.owner.name);
          code.emit(CALL_METHOD(m, style))
        case JVM.invokestatic    =>
          val m = pool.getMemberSymbol(in.nextChar, true); size += 2
          if (isBox(m))
            code.emit(BOX(toTypeKind(m.info.paramTypes.head)))
          else if (isUnbox(m))
            code.emit(UNBOX(toTypeKind(m.info.resultType)))
          else
            code.emit(CALL_METHOD(m, Static(false)))

        case JVM.new_          =>
          code.emit(NEW(REFERENCE(pool.getClassSymbol(in.nextChar))))
          size += 2
        case JVM.newarray      =>
          val kind = in.nextByte match {
            case T_BOOLEAN => BOOL
            case T_CHAR    => CHAR
            case T_FLOAT   => FLOAT
            case T_DOUBLE  => DOUBLE
            case T_BYTE    => BYTE
            case T_SHORT   => SHORT
            case T_INT     => INT
            case T_LONG    => LONG
          }
          size += 1
          code.emit(CREATE_ARRAY(kind, 1))

        case JVM.anewarray     =>
          val tpe = pool.getClassOrArrayType(in.nextChar); size += 2
          code.emit(CREATE_ARRAY(toTypeKind(tpe), 1))

        case JVM.arraylength   => code.emit(CALL_PRIMITIVE(ArrayLength(ObjectReference))); // the kind does not matter
        case JVM.athrow        => code.emit(THROW(definitions.ThrowableClass))
        case JVM.checkcast     =>
          code.emit(CHECK_CAST(toTypeKind(pool.getClassOrArrayType(in.nextChar)))); size += 2
        case JVM.instanceof    =>
          code.emit(IS_INSTANCE(toTypeKind(pool.getClassOrArrayType(in.nextChar)))); size += 2
        case JVM.monitorenter  => code.emit(MONITOR_ENTER())
        case JVM.monitorexit   => code.emit(MONITOR_EXIT())
        case JVM.wide          =>
          size += 1
          toUnsignedByte(in.nextByte) match {
            case JVM.iload  => loadLocal (in.nextChar, INT   ); size += 2
            case JVM.lload  => loadLocal (in.nextChar, LONG  ); size += 2
            case JVM.fload  => loadLocal (in.nextChar, FLOAT ); size += 2
            case JVM.dload  => loadLocal (in.nextChar, DOUBLE); size += 2
            case JVM.aload  => loadLocal (in.nextChar, ObjectReference); size += 2
            case JVM.istore => storeLocal(in.nextChar, INT   ); size += 2
            case JVM.lstore => storeLocal(in.nextChar, LONG  ); size += 2
            case JVM.fstore => storeLocal(in.nextChar, FLOAT ); size += 2
            case JVM.dstore => storeLocal(in.nextChar, DOUBLE); size += 2
            case JVM.astore => storeLocal(in.nextChar, ObjectReference); size += 2
            case JVM.ret => sys.error("Cannot handle jsr/ret")
            case JVM.iinc =>
              size += 4
              val local = code.getLocal(in.nextChar, INT)
              code.emit(CONSTANT(Constant(in.nextChar)))
              code.emit(CALL_PRIMITIVE(Arithmetic(ADD, INT)))
              code.emit(STORE_LOCAL(local))
            case _ => sys.error("Invalid 'wide' operand")
          }

        case JVM.multianewarray =>
          size += 3
          val tpe = toTypeKind(pool getClassOrArrayType in.nextChar)
          val dim = in.nextByte
//          assert(dim == 1, "Cannot handle multidimensional arrays yet.")
          code emit CREATE_ARRAY(tpe, dim)

        case JVM.ifnull    => code emit LCZJUMP(parseJumpTarget, pc + size, EQ, ObjectReference)
        case JVM.ifnonnull => code emit LCZJUMP(parseJumpTarget, pc + size, NE, ObjectReference)
        case JVM.goto_w    => code emit LJUMP(parseJumpTargetW)
        case JVM.jsr_w     => sys.error("Cannot handle jsr/ret")

//        case _ => sys.error("Unknown bytecode")
      }
      pc += size
    }

    // add parameters
    var idx = if (method.isStatic) 0 else 1
    for (t <- method.symbol.tpe.paramTypes) {
      val kind = toTypeKind(t)
      this.method addParam code.enterParam(idx, kind)
      val width = if (kind.isWideType) 2 else 1
      idx += width
    }

    pc = 0
    while (pc < codeLength) parseInstruction

    val exceptionEntries = in.nextChar.toInt
    code.containsEHs = (exceptionEntries != 0)
    var i = 0
    while (i < exceptionEntries) {
      // skip start end PC
      in.skip(4)
      // read the handler PC
      code.jmpTargets += in.nextChar
      // skip the exception type
      in.skip(2)
      i += 1
    }
    skipAttributes()

    code.toBasicBlock
    assert(method.hasCode, method)
    // reverse parameters, as they were prepended during code generation
    method.params = method.params.reverse

    if (code.containsDUPX)
      code.resolveDups()

    if (code.containsNEW)
      code.resolveNEWs()
  }

  /** Note: these methods are different from the methods of the same name found
   *  in Definitions.  These test whether a symbol represents one of the boxTo/unboxTo
   *  methods found in BoxesRunTime.  The others test whether a symbol represents a
   *  synthetic method from one of the fake companion classes of the primitive types,
   *  such as Int.box(5).
   */
  def isBox(m: Symbol): Boolean =
    (m.owner == definitions.BoxesRunTimeClass
        && m.name.startsWith("boxTo"))

  def isUnbox(m: Symbol): Boolean =
    (m.owner == definitions.BoxesRunTimeClass
        && m.name.startsWith("unboxTo"))

  /** Return the icode class that should include members with the given flags.
   *  There are two possible classes, the static part and the instance part.
   */
  def getCode(flags: Int): IClass =
    if (isScalaModule) staticCode
    else if ((flags & JAVA_ACC_STATIC) != 0) staticCode
    else instanceCode

  class LinearCode {
    var instrs: ListBuffer[(Int, Instruction)] = new ListBuffer
    var jmpTargets: mutable.Set[Int] = perRunCaches.newSet[Int]()
    var locals: mutable.Map[Int, List[(Local, TypeKind)]] = perRunCaches.newMap()

    var containsDUPX = false
    var containsNEW  = false
    var containsEHs  = false

    def emit(i: Instruction) {
      instrs += ((pc, i))
      if (i.isInstanceOf[DupX])
        containsDUPX = true
      if (i.isInstanceOf[opcodes.NEW])
        containsNEW = true
    }

    /** Break this linear code in basic block representation
     *  As a side effect, it sets the `code` field of the current
     */
    def toBasicBlock: Code = {
      import opcodes._

      val code = new Code(method)
      method.setCode(code)
      method.bytecodeHasEHs = containsEHs
      var bb = code.startBlock

      def makeBasicBlocks: mutable.Map[Int, BasicBlock] =
        mutable.Map(jmpTargets.toSeq map (_ -> code.newBlock): _*)

      val blocks = makeBasicBlocks
      var otherBlock: BasicBlock = NoBasicBlock
      var disableJmpTarget = false

      for ((pc, instr) <- instrs.iterator) {
//        Console.println("> " + pc + ": " + instr);
        if (jmpTargets(pc)) {
          otherBlock = blocks(pc)
          if (!bb.closed && otherBlock != bb) {
            bb.emit(JUMP(otherBlock))
            bb.close
//            Console.println("\t> closing bb: " + bb)
          }
          bb = otherBlock
//          Console.println("\t> entering bb: " + bb)
        }
        instr match {
          case LJUMP(target) =>
            otherBlock = blocks(target)
            bb.emitOnly(JUMP(otherBlock))

          case LCJUMP(success, failure, cond, kind) =>
            otherBlock = blocks(success)
            val failBlock = blocks(failure)
            bb.emitOnly(CJUMP(otherBlock, failBlock, cond, kind))

          case LCZJUMP(success, failure, cond, kind) =>
            otherBlock = blocks(success)
            val failBlock = blocks(failure)
            bb.emitOnly(CZJUMP(otherBlock, failBlock, cond, kind))

          case LSWITCH(tags, targets) =>
            bb.emitOnly(SWITCH(tags, targets map blocks))

          case RETURN(_) =>
            bb emitOnly instr

          case THROW(clasz) =>
            bb emitOnly instr

          case _ =>
            bb emit instr
        }
      }

      method.code
    }

    def resolveDups() {
      import opcodes._

      val tfa = new analysis.MethodTFA() {
        import analysis._
        import analysis.typeFlowLattice.IState

        /** Abstract interpretation for one instruction. */
        override def mutatingInterpret(out: typeFlowLattice.Elem, i: Instruction): typeFlowLattice.Elem = {
          val bindings = out.vars
          val stack = out.stack
          import stack.push
          i match {
            case DUP_X1 =>
              val (one, two) = stack.pop2
              push(one); push(two); push(one);

            case DUP_X2 =>
              val (one, two, three) = stack.pop3
              push(one); push(three); push(two); push(one);

            case DUP2_X1 =>
              val (one, two) = stack.pop2
              if (one.isWideType) {
                push(one); push(two); push(one);
              } else {
                val three = stack.pop
                push(two); push(one); push(three); push(two); push(one);
              }

            case DUP2_X2 =>
              val (one, two) = stack.pop2
              if (one.isWideType && two.isWideType) {
                push(one); push(two); push(one);
              } else if (one.isWideType) {
                val three = stack.pop
                assert(!three.isWideType, "Impossible")
                push(one); push(three); push(two); push(one);
              } else {
                val three = stack.pop
                if (three.isWideType) {
                  push(two); push(one); push(one); push(three); push(two); push(one);
                } else {
                  val four = stack.pop
                  push(two); push(one); push(four); push(one); push(three); push(two); push(one);
                }
              }

            case _ =>
              super.mutatingInterpret(out, i)
          }
          out
        }
      }

//      method.dump
      tfa.init(method)
      tfa.run
      for (bb <- linearizer.linearize(method)) {
        var info = tfa.in(bb)
        for (i <- bb.toList) {
          i match {
            case DUP_X1 =>
              val one = info.stack.types(0)
              val two = info.stack.types(1)
              assert(!one.isWideType, "DUP_X1 expects values of size 1 on top of stack " + info.stack)
              val tmp1 = freshLocal(one)
              val tmp2 = freshLocal(two)
              bb.replaceInstruction(i, List(STORE_LOCAL(tmp1),
                  STORE_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1),
                  LOAD_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1)));

            case DUP_X2 =>
              val one = info.stack.types(0)
              val two = info.stack.types(1)
              assert (!one.isWideType, "DUP_X2 expects values of size 1 on top of stack " + info.stack)
              val tmp1 = freshLocal(one)
              val tmp2 = freshLocal(two)
              if (two.isWideType)
                bb.replaceInstruction(i, List(STORE_LOCAL(tmp1),
                  STORE_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1),
                  LOAD_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1)));
              else {
                val tmp3 = freshLocal(info.stack.types(2));
                bb.replaceInstruction(i, List(STORE_LOCAL(tmp1),
                  STORE_LOCAL(tmp2),
                  STORE_LOCAL(tmp3),
                  LOAD_LOCAL(tmp1),
                  LOAD_LOCAL(tmp3),
                  LOAD_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1)));
              }

            case DUP2_X1 =>
              val one = info.stack.types(0)
              val two = info.stack.types(1)
              val tmp1 = freshLocal(one);
              val tmp2 = freshLocal(two);
              if (one.isWideType) {
                assert(!two.isWideType, "Impossible")
                bb.replaceInstruction(i, List(STORE_LOCAL(tmp1),
                  STORE_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1),
                  LOAD_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1)));
              } else {
                val tmp3 = freshLocal(info.stack.types(2))
                bb.replaceInstruction(i, List(STORE_LOCAL(tmp1),
                  STORE_LOCAL(tmp2),
                  STORE_LOCAL(tmp3),
                  LOAD_LOCAL(tmp1),
                  LOAD_LOCAL(tmp3),
                  LOAD_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1)));
              }

            case DUP2_X2 =>
              val one = info.stack.types(0)
              val two = info.stack.types(1)
              val tmp1 = freshLocal(one)
              val tmp2 = freshLocal(two)
              if (one.isWideType && two.isWideType) {
                bb.replaceInstruction(i, List(STORE_LOCAL(tmp1),
                  STORE_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1),
                  LOAD_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1)));
              } else if (one.isWideType) {
                val three = info.stack.types(2)
                assert(!two.isWideType && !three.isWideType, "Impossible")
                val tmp3 = freshLocal(three);
                bb.replaceInstruction(i, List(STORE_LOCAL(tmp1),
                  STORE_LOCAL(tmp2),
                  STORE_LOCAL(tmp3),
                  LOAD_LOCAL(tmp1),
                  LOAD_LOCAL(tmp3),
                  LOAD_LOCAL(tmp2),
                  LOAD_LOCAL(tmp1)));
              } else {
                val three = info.stack.types(2)
                val tmp3 = freshLocal(three);
                if (three.isWideType) {
                  bb.replaceInstruction(i, List(STORE_LOCAL(tmp1),
                      STORE_LOCAL(tmp2),
                      STORE_LOCAL(tmp3),
                      LOAD_LOCAL(tmp2),
                      LOAD_LOCAL(tmp1),
                      LOAD_LOCAL(tmp3),
                      LOAD_LOCAL(tmp2),
                      LOAD_LOCAL(tmp1)));
                } else {
                  val four = info.stack.types(3)
                  val tmp4 = freshLocal(three);
                  assert(!four.isWideType, "Impossible")
                  bb.replaceInstruction(i, List(STORE_LOCAL(tmp1),
                      STORE_LOCAL(tmp2),
                      STORE_LOCAL(tmp3),
                      STORE_LOCAL(tmp4),
                      LOAD_LOCAL(tmp2),
                      LOAD_LOCAL(tmp1),
                      LOAD_LOCAL(tmp4),
                      LOAD_LOCAL(tmp3),
                      LOAD_LOCAL(tmp2),
                      LOAD_LOCAL(tmp1)));
                }
              }
            case _ =>
          }
          info = tfa.interpret(info, i)
        }
      }
    }

    /** Recover def-use chains for NEW and initializers. */
    def resolveNEWs() {
      import opcodes._
      val rdef = new reachingDefinitions.ReachingDefinitionsAnalysis
      rdef.init(method)
      rdef.run

      for (bb <- method.code.blocks ; (i, idx) <- bb.toList.zipWithIndex) i match {
        case cm @ CALL_METHOD(m, Static(true)) if m.isClassConstructor =>
          def loop(bb0: BasicBlock, idx0: Int, depth: Int = 0): Unit = {
            rdef.findDefs(bb0, idx0, 1, depth) match {
              case ((bb1, idx1)) :: _ =>
                bb1(idx1) match {
                  case _: DUP   => loop(bb1, idx1, 0)
                  case x: NEW   => x.init = cm
                  case _: THIS  => () // super constructor call
                  case producer => dumpMethodAndAbort(method, "producer: " + producer)
                }
              case _ => ()
            }
          }
          loop(bb, idx, m.info.paramTypes.length)

        case _ => ()
      }
    }

    /** Return the local at given index, with the given type. */
    def getLocal(idx: Int, kind: TypeKind): Local = {
      assert(idx < maxLocals, "Index too large for local variable.")

      def checkValidIndex() {
        locals.get(idx - 1) match {
          case Some(others) if others exists (_._2.isWideType) =>
            global.globalError("Illegal index: " + idx + " points in the middle of another local")
          case _ => ()
        }
        kind match {
          case LONG | DOUBLE if (locals.isDefinedAt(idx + 1)) =>
            global.globalError("Illegal index: " + idx + " overlaps " + locals(idx + 1) + "\nlocals: " + locals)
          case _ => ()
        }
      }

      locals.get(idx) match {
        case Some(ls) =>
          val l = ls find { loc => loc._2 <:< kind }
          l match {
            case Some((loc, _)) => loc
            case None =>
              val l = freshLocal(kind)
              locals(idx) = (l, kind) :: locals(idx)
              log("Expected kind " + kind + " for local " + idx +
                " but only " + ls + " found. Added new local.")
              l
          }
        case None =>
          checkValidIndex
          val l = freshLocal(idx, kind, false)
          log("Added new local for idx " + idx + ": " + kind)
          locals += (idx -> List((l, kind)))
          l
      }
    }

    override def toString(): String = instrs.toList.mkString("", "\n", "")

    /** Return a fresh Local variable for the given index.
     */
    private def freshLocal(idx: Int, kind: TypeKind, isArg: Boolean) = {
      val sym = method.symbol.newVariable(newTermName("loc" + idx)).setInfo(kind.toType);
      val l = new Local(sym, kind, isArg)
      method.addLocal(l)
      l
    }

    private var count = 0

    /** Invent a new local, with a new index value outside the range of
     *  the original method. */
    def freshLocal(kind: TypeKind): Local = {
      count += 1
      freshLocal(maxLocals + count, kind, false)
    }

    /** add a method param with the given index. */
    def enterParam(idx: Int, kind: TypeKind) = {
      val sym = method.symbol.newVariable(newTermName("par" + idx)).setInfo(kind.toType)
      val l = new Local(sym, kind, true)
      assert(!locals.isDefinedAt(idx), locals(idx))
      locals += (idx -> List((l, kind)))
      l
    }

    /** Base class for branch instructions that take addresses. */
    abstract class LazyJump(pc: Int) extends Instruction {
      override def toString() = "LazyJump " + pc
      jmpTargets += pc
    }

    case class LJUMP(pc: Int) extends LazyJump(pc);
    case class LCJUMP(success: Int, failure: Int, cond: TestOp, kind: TypeKind)
      extends LazyJump(success) {
      override def toString(): String = "LCJUMP (" + kind + ") " + success + " : " + failure

      jmpTargets += failure
    }

    case class LCZJUMP(success: Int, failure: Int, cond: TestOp, kind: TypeKind)
      extends LazyJump(success) {
      override def toString(): String = "LCZJUMP (" + kind + ") " + success + " : " + failure

      jmpTargets += failure
    }

    case class LSWITCH(tags: List[List[Int]], targets: List[Int]) extends LazyJump(targets.head) {
      override def toString(): String = "LSWITCH (tags: " + tags + ") targets: " + targets

      jmpTargets ++= targets.tail
    }

    /** Duplicate and exchange pseudo-instruction. Should be later
     *  replaced by proper ICode */
    abstract class DupX extends Instruction

    case object DUP_X1 extends DupX
    case object DUP_X2 extends DupX
    case object DUP2_X1 extends DupX
    case object DUP2_X2 extends DupX
  }
}
