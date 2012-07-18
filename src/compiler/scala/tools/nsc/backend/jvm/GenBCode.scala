/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.collection.{ mutable, immutable }
import scala.collection.mutable.{ ListBuffer, Buffer }
import scala.tools.nsc.symtab._
import scala.annotation.switch
import scala.tools.asm
import asm.tree.{JumpInsnNode, LabelNode, ClassNode}

/** Prepare in-memory representations of classfiles using the ASM Tree API, and serialize them to disk.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 */
abstract class GenBCode extends BCodeUtils {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions._

  val phaseName = "bcode"

  override def newPhase(prev: Phase) = new BCodePhase(prev)

  class BCodePhase(prev: Phase)
    extends StdPhase(prev)
    with    BCInitGen
    with    BCJGenSigGen
    with    BCCommonPhase {

    override def name = phaseName
    override def description = "Generate bytecode from ASTs"
    override def erasedTypes = true

    private var bytecodeWriter  : BytecodeWriter   = null
    private var mirrorCodeGen   : JMirrorBuilder   = null
    private var beanInfoCodeGen : JBeanInfoBuilder = null

    /* ---------------- what is currently being visited ---------------- */

    // current compilation unit and package
    private var cunit: CompilationUnit     = null
    private val pkg = new mutable.Stack[String]
    // current class
    private var cnode: asm.tree.ClassNode  = null
    private var thisName: String           = null // the internal name of the class being emitted
    private var claszSymbol: Symbol        = null
    // current method
    private var mnode: asm.tree.MethodNode = null
    private var jMethodName: String        = null
    private var isModuleInitialized        = false // in GenASM this is local to genCode(), ie should get false whenever a new method is emitted (including fabricated ones eg addStaticInit())

    // bookkeeping for method-local vars and params
    private val locIdx = mutable.Map.empty[Symbol, Int] // (local-or-param-sym -> index-of-local-in-method)
    private var nxtIdx = -1 // next available index for local-var
    private def sizeOf(k: TypeKind): Int = if(k.isWideType) 2 else 1
    private def index(sym: Symbol): Int = {
      locIdx.getOrElseUpdate(sym, {
        val idx = nxtIdx;
        assert(idx != -1, "GenBCode.index() run before GenBCode.genDedDef()")
        nxtIdx += sizeOf(toTypeKind(sym.info))
        idx
      })
    }

    override def getCurrentCUnit(): CompilationUnit = { cunit }

    override def run() {
      scalaPrimitives.init
      bytecodeWriter  = initBytecodeWriter(cleanup.getEntryPoints)
      mirrorCodeGen   = new JMirrorBuilder(bytecodeWriter)
      beanInfoCodeGen = new JBeanInfoBuilder(bytecodeWriter)
      super.run()
      bytecodeWriter.close()
      reverseJavaName.clear()
    }

    override def apply(unit: CompilationUnit): Unit = {
      this.cunit = unit
      gen(unit.body)
      this.cunit = NoCompilationUnit
    }

    object bc extends JCodeMethodN(BCodePhase.this.StringBuilderClassName) {
      override def jmethod = BCodePhase.this.mnode
    }

    /* ---------------- top-down traversal invoking ASM Tree API along the way ---------------- */

    def gen(tree: Tree) {
      tree match {
        case EmptyTree => ()

        case PackageDef(pid, stats) =>
          pkg push pid.name.toString
          stats foreach gen
          pkg.pop()

        case cd: ClassDef =>
          // mirror class, if needed
          if (isStaticModule(cd.symbol) && isTopLevelModule(cd.symbol)) {
            if (cd.symbol.companionClass == NoSymbol) {
              mirrorCodeGen.genMirrorClass(cd.symbol, cunit)
            } else {
              log("No mirror class for module with linked class: " + cd.symbol.fullName)
            }
          }
          // "plain" class
          genPlainClass(cd)
          // bean info class, if needed
          if (cd.symbol hasAnnotation BeanInfoAttr) {
            beanInfoCodeGen.genBeanInfoClass(
              cd.symbol, cunit,
              fieldSymbols(cd.symbol),
              methodSymbols(cd) filterNot skipMethod
            )
          }

        case ModuleDef(mods, name, impl) =>
          abort("Modules should have been eliminated by refchecks: " + tree)

        case ValDef(mods, name, tpt, rhs) =>
          () // fields are added in the case handler for ClassDef

        case dd : DefDef =>
          if(!skipMethod(dd.symbol)) { genDefDef(dd) }

        case Template(_, _, body) =>
          body foreach gen

        case _ =>
          abort("Illegal tree in gen: " + tree)
      }
    } // end of method gen(Tree)

    /* if you look closely, you'll notice almost no code duplication with JBuilder's `writeIfNotTooBig()` */
    def writeIfNotTooBig(label: String, jclassName: String, cnode: asm.tree.ClassNode, sym: Symbol) {
      try {
        val cw = new CClassWriter(extraProc)
        cnode.accept(cw)
        val arr = cw.toByteArray
        bytecodeWriter.writeClass(label, jclassName, arr, sym)
      } catch {
        case e: java.lang.RuntimeException if(e.getMessage() == "Class file too large!") =>
          // TODO check where ASM throws the equivalent of CodeSizeTooBigException
          log("Skipped class "+jclassName+" because it exceeds JVM limits (it's too big or has methods that are too long).")
      }
    }

    /* ---------------- helper utils for generating classes and fiels ---------------- */

    def genPlainClass(cd: ClassDef) {
      assert(cnode == null, "GenBCode detected nested methods.")
      innerClassBuffer.clear()

      val csym = cd.symbol
      thisName = javaName(csym)
      cnode = new asm.tree.ClassNode()
      initJClass(cnode, csym, thisName, getGenericSignature(csym, csym.owner), cunit)

      /* TODO
       *       val scOpt = c.lookupStaticCtor
       *       isModuleInitialized = false
       *       if (isStaticModule(c.symbol) || isAndroidParcelableClass(c.symbol)) {
       *         addStaticInit(scOpt)
       *       } else if (scOpt.isDefined) {
       *         addStaticInit(scOpt)
       *       }
       **/

      addSerialVUID(csym, cnode)
      addClassFields(csym)
      gen(cd.impl)
      addInnerClasses(csym, cnode)

      /*
       * TODO this is the time for collapsing of jump-chains, dce, locals optimization, etc. on the asm.tree.ClassNode.
       * See Ch. 8. "Method Analysis" in the ASM User Guide, http://download.forge.objectweb.org/asm/asm4-guide.pdf
       **/
      writeIfNotTooBig("" + csym.name, thisName, cnode, csym)
      cnode = null

    } // end of method genPlainClass()

    private def fieldSymbols(cls: Symbol): List[Symbol] = {
      for (f <- cls.info.decls.toList ; if !f.isMethod && f.isTerm && !f.isModule) yield f;
    }

    private def skipMethod(msym: Symbol): Boolean = {
      msym.isStaticConstructor || definitions.isGetClass(msym)
    }

    def addClassFields(cls: Symbol) {
      /** Non-method term members are fields, except for module members. Module
       *  members can only happen on .NET (no flatten) for inner traits. There,
       *  a module symbol is generated (transformInfo in mixin) which is used
       *  as owner for the members of the implementation class (so that the
       *  backend emits them as static).
       *  No code is needed for this module symbol.
       */
      for (f <- fieldSymbols(cls)) {
        val javagensig = getGenericSignature(f, cls)
        val flags = mkFlags(
          javaFieldFlags(f),
          if(isDeprecated(f)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo access flag
        )

        val jfield = new asm.tree.FieldNode(
          flags,
          javaName(f),
          javaType(f.tpe).getDescriptor(),
          javagensig,
          null // no initial value
        )
        cnode.fields.add(jfield)
        emitAnnotations(jfield, f.annotations)
      }

    } // end of method addClassFields()

    /* ---------------- helper utils for generating methods and code ---------------- */

    @inline final def emit(opc: Int) { mnode.visitInsn(opc) }

    def genDefDef(dd: DefDef) {
      assert(mnode == null, "GenBCode detected nested method.")
      val msym = dd.symbol
      // clear method-specific stuff
      locIdx.clear()
          // TODO local-ranges table
          // TODO exh-handlers table

      val DefDef(_, _, _, vparamss, _, rhs) = dd
      assert(vparamss.isEmpty || vparamss.tail.isEmpty, "Malformed parameter list: " + vparamss)
      val isNative = msym.hasAnnotation(definitions.NativeAttr)
      val isAbstractMethod = msym.isDeferred || msym.owner.isInterface

      val params      = vparamss.head
      claszSymbol     = msym.owner
      val Pair(flags, jmethod0) = initJMethod(
        cnode,
        msym, isNative,
        claszSymbol,  claszSymbol.isInterface,
        params.map(p => javaType(p.symbol.info)),
        params.map(p => p.symbol.annotations)
      )
      mnode       = jmethod0.asInstanceOf[asm.tree.MethodNode]
      jMethodName = javaName(msym)
      isModuleInitialized = false

      // add params
      nxtIdx = if (msym.isStaticMember) 0 else 1;
      for (p <- params) {
        val tk = toTypeKind(p.symbol.info)
        locIdx += (p.symbol -> nxtIdx)
        nxtIdx += sizeOf(tk)
      }

      val returnType =
        if (msym.isConstructor) UNIT
        else toTypeKind(msym.info.resultType)

      if (!isAbstractMethod && !isNative) {
        genLoad(rhs, returnType)
        // TODO see JPlainBuilder.addAndroidCreatorCode()
        rhs match {
          case Block(_, Return(_)) => ()
          case Return(_) => ()
          case EmptyTree =>
            globalError("Concrete method has no definition: " + dd + (
              if (settings.debug.value) "(found: " + msym.owner.info.decls.toList.mkString(", ") + ")"
              else "")
            )
          case _ =>
            bc emitRETURN returnType
        }
      }
      mnode = null
    } // end of method genDefDef()

    /**
     * Emits code that adds nothing to the operand stack.
     * Two main cases: `tree` is an assignment,
     * otherwise an `adapt()` to UNIT is performed if needed.
     */
    def genStat(tree: Tree) {
      tree match {
        case Assign(lhs @ Select(_, _), rhs) =>
          val isStatic = lhs.symbol.isStaticMember
          if (!isStatic) { genLoadQualifier(lhs) }
          genLoad(rhs, toTypeKind(lhs.symbol.info))
          bc fieldStore lhs.symbol

        case Assign(lhs, rhs) =>
          val tk = toTypeKind(lhs.symbol.info)
          genLoad(rhs, tk)
          bc.store(index(lhs.symbol), tk)

        case _ =>
          genLoad(tree, UNIT)
      }
    }

    def genThrow(expr: Tree): TypeKind = {
      require(expr.tpe <:< ThrowableClass.tpe, expr.tpe)

      val thrownKind = toTypeKind(expr.tpe)
      genLoad(expr, thrownKind)
      emit(asm.Opcodes.ATHROW) // ICode enters here into enterIgnoreMode, we'll rely instead on DCE at ClassNode level.

      NothingReference // TODO always returns the same, the invoker should know :)
    }

    /** Generate code for primitive arithmetic operations. */
    def genArithmeticOp(tree: Tree, code: Int): TypeKind = {
      val Apply(fun @ Select(larg, _), args) = tree
      var resKind = toTypeKind(larg.tpe)

      assert(args.length <= 1, "Too many arguments for primitive function: " + fun.symbol)
      assert(resKind.isNumericType | resKind == BOOL,
               resKind.toString() + " is not a numeric or boolean type " + "[operation: " + fun.symbol + "]")

      args match {
        // unary operation
        case Nil =>
          genLoad(larg, resKind)
          code match {
            case scalaPrimitives.POS => () // nothing
            case scalaPrimitives.NEG => bc.genPrimitive(Negation(resKind), larg.pos)
            case scalaPrimitives.NOT => bc.genPrimitive(Arithmetic(NOT, resKind), larg.pos)
            case _ => abort("Unknown unary operation: " + fun.symbol.fullName + " code: " + code)
          }

        // binary operation
        case rarg :: Nil =>
          resKind = getMaxType(larg.tpe :: rarg.tpe :: Nil);
          if (scalaPrimitives.isShiftOp(code) || scalaPrimitives.isBitwiseOp(code))
            assert(resKind.isIntegralType | resKind == BOOL,
                   resKind.toString() + " incompatible with arithmetic modulo operation.");

          genLoad(larg, resKind)
          genLoad(rarg, // check .NET size of shift arguments!
                  if (scalaPrimitives.isShiftOp(code)) INT else resKind)

          val primitiveOp = code match {
            case scalaPrimitives.ADD    => Arithmetic(ADD, resKind)
            case scalaPrimitives.SUB    => Arithmetic(SUB, resKind)
            case scalaPrimitives.MUL    => Arithmetic(MUL, resKind)
            case scalaPrimitives.DIV    => Arithmetic(DIV, resKind)
            case scalaPrimitives.MOD    => Arithmetic(REM, resKind)
            case scalaPrimitives.OR     => Logical(OR, resKind)
            case scalaPrimitives.XOR    => Logical(XOR, resKind)
            case scalaPrimitives.AND    => Logical(AND, resKind)
            case scalaPrimitives.LSL    => Shift(LSL, resKind)
            case scalaPrimitives.LSR    => Shift(LSR, resKind)
            case scalaPrimitives.ASR    => Shift(ASR, resKind)
            case _                      => abort("Unknown primitive: " + fun.symbol + "[" + code + "]")
          }
          bc.genPrimitive(primitiveOp, tree.pos)

        case _ =>
          abort("Too many arguments for primitive function: " + tree)
      }
      resKind
    }

    /** Generate primitive array operations. */
    def genArrayOp(tree: Tree, code: Int, expectedType: TypeKind): TypeKind = {
      import scalaPrimitives._
      val Apply(Select(arrayObj, _), args) = tree
      val k = toTypeKind(arrayObj.tpe)
      val ARRAY(elem) = k
      genLoad(arrayObj, k)
      val elementType = typeOfArrayOp.getOrElse(code, abort("Unknown operation on arrays: " + tree + " code: " + code))

      var generatedType = expectedType

      if (scalaPrimitives.isArrayGet(code)) {
        // load argument on stack
        assert(args.length == 1, "Too many arguments for array get operation: " + tree);
        genLoad(args.head, INT)
        generatedType = elem
        bc.aload(elementType)
      }
      else if (scalaPrimitives.isArraySet(code)) {
        assert(args.length == 2, "Too many arguments for array set operation: " + tree);
        genLoad(args.head, INT)
        genLoad(args.tail.head, toTypeKind(args.tail.head.tpe))
        // the following line should really be here, but because of bugs in erasure
        // we pretend we generate whatever type is expected from us.
        //generatedType = UNIT
        bc.astore(elementType)
      }
      else {
        generatedType = INT
        emit(asm.Opcodes.ARRAYLENGTH)
      }

      generatedType
    }

    def genSynchronized(tree: Apply, expectedType: TypeKind): TypeKind = {
      ???
    }

    def genLoadIf(tree: If, expectedType: TypeKind): TypeKind = {
      val If(condp, thenp, elsep) = tree
      genLoad(condp, BOOL)
      val postThenPoint = new asm.tree.LabelNode()
      val jmpOverThen   = new asm.tree.JumpInsnNode(asm.Opcodes.IFEQ, postThenPoint)
      mnode.instructions.add(jmpOverThen)

      val thenKind = toTypeKind(thenp.tpe)
      val elseKind = if (elsep.isEmpty) UNIT else toTypeKind(elsep.tpe)
      def hasUnitBranch = (thenKind == UNIT || elseKind == UNIT)
      val resKind  = if (hasUnitBranch) UNIT else toTypeKind(tree.tpe)

      genLoad(thenp, resKind)
      val postIf = new asm.tree.LabelNode()
      if (!elsep.isEmpty) {
        val jmpOverElse = new asm.tree.JumpInsnNode(asm.Opcodes.GOTO, postIf)
        mnode.instructions.add(jmpOverElse)
      }
      mnode.instructions.add(postThenPoint)
      if (!elsep.isEmpty) {
        genLoad(elsep, resKind)
        mnode.instructions.add(postIf)
      }

      resKind
    }

    def genLoadTry(tree: Try) {
      ??? // TODO
    }

    def genPrimitiveOp(tree: Apply, expectedType: TypeKind): TypeKind = {
      val sym = tree.symbol
      val Apply(fun @ Select(receiver, _), args) = tree
      val code = scalaPrimitives.getPrimitive(sym, receiver.tpe)

      import scalaPrimitives.{isArithmeticOp, isArrayOp, isLogicalOp, isComparisonOp}

      if (isArithmeticOp(code))                genArithmeticOp(tree, code)
      else if (code == scalaPrimitives.CONCAT) genStringConcat(tree)
      else if (code == scalaPrimitives.HASH)   genScalaHash(receiver)
      else if (isArrayOp(code))                genArrayOp(tree, code, expectedType)
      else if (isLogicalOp(code) || isComparisonOp(code)) {
        genLoad(tree, BOOL)
        BOOL
      }
      else if (code == scalaPrimitives.SYNCHRONIZED)
        genSynchronized(tree, expectedType)
      else if (scalaPrimitives.isCoercion(code)) {
        genLoad(receiver, toTypeKind(receiver.tpe))
        genCoercion(tree, code)
        scalaPrimitives.generatedKind(code)
      }
      else abort(
        "Primitive operation not handled yet: " + sym.fullName + "(" +
        fun.symbol.simpleName + ") " + " at: " + (tree.pos)
      )
    }

    /** Generate code for trees that produce values on the stack */
    def genLoad(tree: Tree, expectedType: TypeKind) {
      ???
    }

    def adapt(from: TypeKind, to: TypeKind, pos: Position): Unit = {
      if (!(from <:< to) && !(from == NullReference && to == NothingReference)) {
        to match {
          case UNIT => bc drop from
          case _    => bc.emitT2T(from, to)
        }
      } else if (from == NothingReference) {
        emit(asm.Opcodes.ATHROW) // ICode enters here into enterIgnoreMode, we'll rely instead on DCE at ClassNode level.
      } else if (from == NullReference) {
        bc drop from
        mnode.visitInsn(asm.Opcodes.ACONST_NULL)
      }
      else if (from == ThrowableReference && !(ThrowableClass.tpe <:< to.toType)) {
        bc checkCast to
      }
      else (from, to) match  {
        case (BYTE, LONG) | (SHORT, LONG) | (CHAR, LONG) | (INT, LONG) => bc.emitT2T(INT, LONG)
        case _ => ()
      }
    }

    /** Emit code to Load the qualifier of `tree` on top of the stack. */
    def genLoadQualifier(tree: Tree) {
      tree match {
        case Select(qualifier, _) => genLoad(qualifier, toTypeKind(qualifier.tpe))
        case _                    => abort("Unknown qualifier " + tree)
      }
    }

    /** Generate code that loads args into label parameters. */
    def genLoadLabelArguments(args: List[Tree], labelSym: Symbol) {
      ???
    }

    def genLoadArguments(args: List[Tree], tpes: List[Type]) {
      ???
    }

    def genLoadModule(tree: Tree) {
      // Working around SI-5604.  Rather than failing the compile when we see
      // a package here, check if there's a package object.
      val module = ( // TODO code duplicate from GenICode
        if (!tree.symbol.isPackageClass) tree.symbol
        else tree.symbol.info.member(nme.PACKAGE) match {
          case NoSymbol => assert(false, "Cannot use package as value: " + tree) ; NoSymbol
          case s        => debugwarn("Bug: found package class where package object expected.  Converting.") ; s.moduleClass
        }
      )

      if (claszSymbol == module.moduleClass && jMethodName != nme.readResolve.toString) { // TODO code duplicate from GenASM
        mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
      } else {
        mnode.visitFieldInsn(
          asm.Opcodes.GETSTATIC,
          javaName(module) /* + "$" */ ,
          strMODULE_INSTANCE_FIELD,
          descriptor(module)
        )
      }
    }

    def genConversion(from: TypeKind, to: TypeKind, cast: Boolean) = {
      if (cast) { bc.emitT2T(from, to) }
      else {
        bc drop from
        bc genConstant Constant(from == to)
      }
    }

    def genCast(from: TypeKind, to: TypeKind, cast: Boolean) {
      if(cast) { bc checkCast  to }
      else     { bc isInstance to }
    }

    def getZeroOf(k: TypeKind): Constant = k match {
      case UNIT            => Constant(())
      case BOOL            => Constant(false)
      case BYTE            => Constant(0: Byte)
      case SHORT           => Constant(0: Short)
      case CHAR            => Constant(0: Char)
      case INT             => Constant(0: Int)
      case LONG            => Constant(0: Long)
      case FLOAT           => Constant(0.0f)
      case DOUBLE          => Constant(0.0d)
      case REFERENCE(cls)  => Constant(null: Any)
      case ARRAY(elem)     => Constant(null: Any)
      case BOXED(_)        => Constant(null: Any)
      case ConcatClass     => abort("no zero of ConcatClass")
    }


    /** Is the given symbol a primitive operation? */
    def isPrimitive(fun: Symbol): Boolean = scalaPrimitives.isPrimitive(fun)

    /* Given `code` reports the src TypeKind of the coercion indicated by `code`.
     * To find the dst TypeKind, `ScalaPrimitives.generatedKind(code)` can be used. */
    @inline private final
    def coercionFrom(code: Int): TypeKind = {
      import scalaPrimitives._
      (code: @switch) match {
        case B2B | B2C | B2S | B2I | B2L | B2F | B2D => BYTE
        case S2B | S2S | S2C | S2I | S2L | S2F | S2D => SHORT
        case C2B | C2S | C2C | C2I | C2L | C2F | C2D => CHAR
        case I2B | I2S | I2C | I2I | I2L | I2F | I2D => INT
        case L2B | L2S | L2C | L2I | L2L | L2F | L2D => LONG
        case F2B | F2S | F2C | F2I | F2L | F2F | F2D => FLOAT
        case D2B | D2S | D2C | D2I | D2L | D2F | D2D => DOUBLE
      }
    }

    /** Generate coercion denoted by "code" */
    def genCoercion(tree: Tree, code: Int) = {
      import scalaPrimitives._
      (code: @switch) match {
        case B2B | S2S | C2C | I2I | L2L | F2F | D2D => ()
        case _ =>
          val from = coercionFrom(code)
          val to   = generatedKind(code)
          bc.emitT2T(from, to)
      }
    }

    /** The Object => String overload. */
    private lazy val String_valueOf: Symbol = getMember(StringModule, nme.valueOf) filter (sym =>
      sym.info.paramTypes match {
        case List(pt) => pt.typeSymbol == ObjectClass
        case _        => false
      }
    )

    def genStringConcat(tree: Tree): TypeKind = {

      liftStringConcat(tree) match {

        // Optimization for expressions of the form "" + x.  We can avoid the StringBuilder.
        case List(Literal(Constant("")), arg) =>
          genLoad(arg, ObjectReference)
          genCallMethod(String_valueOf, Static(false))

        case concatenations =>
          bc.genPrimitive(StartConcat, tree.pos)
          for (elem <- concatenations) {
            val kind = toTypeKind(elem.tpe)
            genLoad(elem, kind)
            bc.genPrimitive(StringConcat(kind), elem.pos)
          }
          bc.genPrimitive(EndConcat, tree.pos)

      }

      StringReference
    }

    def genCallMethod(method: Symbol, style: InvokeStyle, hostClass: Symbol = null) {

      val hostSymbol = if(hostClass == null) method.owner else hostClass;

      isModuleInitialized =
        bc.genCallMethod(
          method,      style,      jMethodName,
          claszSymbol, hostSymbol, thisName,    isModuleInitialized
        )

    } // end of genCode()'s genCallMethod()

    /** Generate the scala ## method. */
    def genScalaHash(tree: Tree): TypeKind = {
      ???
      INT
    }

    /**
     * Returns a list of trees that each should be concatenated, from left to right.
     * It turns a chained call like "a".+("b").+("c") into a list of arguments.
     */
    def liftStringConcat(tree: Tree): List[Tree] = tree match { // TODO de-duplicate with GenICode
      case Apply(fun @ Select(larg, method), rarg) =>
        if (isPrimitive(fun.symbol) &&
            scalaPrimitives.getPrimitive(fun.symbol) == scalaPrimitives.CONCAT)
          liftStringConcat(larg) ::: rarg
        else
          List(tree)
      case _ =>
        List(tree)
    }

    /** Some useful equality helpers. */
    def isNull(t: Tree) = PartialFunction.cond(t) { case Literal(Constant(null)) => true } // TODO de-duplicate with GenICode

    /* If l or r is constant null, returns the other ; otherwise null */
    def ifOneIsNull(l: Tree, r: Tree) = if (isNull(l)) r else if (isNull(r)) l else null // TODO de-duplicate with GenICode

    /**
     * Generate the "==" code for object references. It is equivalent of
     * if (l eq null) r eq null else l.equals(r);
     *
     * @param l       left-hand side of the '=='
     * @param r       right-hand side of the '=='
     * @param ctx     current context
     * @param thenCtx target context if the comparison yields true  TODO
     * @param elseCtx target context if the comparison yields false TODO
     */
    def genEqEqPrimitive(l: Tree, r: Tree) {
      ???
    }

    /** Does this tree have a try-catch block? */
    def mayCleanStack(tree: Tree): Boolean = tree exists { // TODO de-duplicate with GenICode
      case Try(_, _, _) => true
      case _            => false
    }

    def getMaxType(ts: List[Type]): TypeKind = // TODO de-duplicate with GenICode
      ts map toTypeKind reduceLeft (_ maxType _)

    abstract class Cleanup(val value: AnyRef) {
      def contains(x: AnyRef) = value == x
    }
    case class MonitorRelease(v: Symbol) extends Cleanup(v) { }
    case class Finalizer(f: Tree) extends Cleanup (f) { }


  } // end of class BCodePhase

} // end of class GenBCode
