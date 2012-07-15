/* NSC -- new Scala compiler
 * Copyright 2005-2011 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala.tools.nsc
package backend.jvm

import java.nio.ByteBuffer
import scala.collection.{ mutable, immutable }
import scala.reflect.internal.pickling.{ PickleFormat, PickleBuffer }
import scala.tools.nsc.symtab._
import scala.tools.nsc.io.AbstractFile

import scala.tools.asm
import asm.Label

/**
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded
 *
 */
abstract class BCodeUtils extends SubComponent with BytecodeWriters {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions._

  var pickledBytes = 0 // statistics

  // Don't put this in per run caches. Contains entries for classes as well as members.
  val javaNameCache = new mutable.WeakHashMap[Symbol, Name]() ++= List(
    NothingClass        -> binarynme.RuntimeNothing,
    RuntimeNothingClass -> binarynme.RuntimeNothing,
    NullClass           -> binarynme.RuntimeNull,
    RuntimeNullClass    -> binarynme.RuntimeNull
  )

  // unlike javaNameCache, reverseJavaName contains entries only for class symbols and their internal names.
  val reverseJavaName = mutable.Map.empty[String, Symbol] ++= List(
    binarynme.RuntimeNothing.toString() -> RuntimeNothingClass, // RuntimeNothingClass is the bytecode-level return type of Scala methods with Nothing return-type.
    binarynme.RuntimeNull.toString()    -> RuntimeNullClass
  )

  def mkFlags(args: Int*) = args.foldLeft(0)(_ | _)

  @inline final def hasPublicBitSet(flags: Int) = ((flags & asm.Opcodes.ACC_PUBLIC) != 0)

  @inline final def isRemote(s: Symbol) = (s hasAnnotation RemoteAttr)

  /**
   * Return the Java modifiers for the given symbol.
   * Java modifiers for classes:
   *  - public, abstract, final, strictfp (not used)
   * for interfaces:
   *  - the same as for classes, without 'final'
   * for fields:
   *  - public, private (*)
   *  - static, final
   * for methods:
   *  - the same as for fields, plus:
   *  - abstract, synchronized (not used), strictfp (not used), native (not used)
   *
   *  (*) protected cannot be used, since inner classes 'see' protected members,
   *      and they would fail verification after lifted.
   */
  def javaFlags(sym: Symbol): Int = {
    // constructors of module classes should be private
    // PP: why are they only being marked private at this stage and not earlier?
    val privateFlag =
      sym.isPrivate || (sym.isPrimaryConstructor && isTopLevelModule(sym.owner))

    // Final: the only fields which can receive ACC_FINAL are eager vals.
    // Neither vars nor lazy vals can, because:
    //
    // Source: http://docs.oracle.com/javase/specs/jls/se7/html/jls-17.html#jls-17.5.3
    // "Another problem is that the specification allows aggressive
    // optimization of final fields. Within a thread, it is permissible to
    // reorder reads of a final field with those modifications of a final
    // field that do not take place in the constructor."
    //
    // A var or lazy val which is marked final still has meaning to the
    // scala compiler. The word final is heavily overloaded unfortunately;
    // for us it means "not overridable". At present you can't override
    // vars regardless; this may change.
    //
    // The logic does not check .isFinal (which checks flags for the FINAL flag,
    // and includes symbols marked lateFINAL) instead inspecting rawflags so
    // we can exclude lateFINAL. Such symbols are eligible for inlining, but to
    // avoid breaking proxy software which depends on subclassing, we do not
    // emit ACC_FINAL.
    // Nested objects won't receive ACC_FINAL in order to allow for their overriding.

    val finalFlag = (
         (sym.hasFlag(Flags.FINAL) || isTopLevelModule(sym))
      && !sym.enclClass.isInterface
      && !sym.isClassConstructor
      && !sym.isMutable // lazy vals and vars both
    )

    // Primitives are "abstract final" to prohibit instantiation
    // without having to provide any implementations, but that is an
    // illegal combination of modifiers at the bytecode level so
    // suppress final if abstract if present.
    import asm.Opcodes._
    mkFlags(
      if (privateFlag) ACC_PRIVATE else ACC_PUBLIC,
      if (sym.isDeferred || sym.hasAbstractFlag) ACC_ABSTRACT else 0,
      if (sym.isInterface) ACC_INTERFACE else 0,
      if (finalFlag && !sym.hasAbstractFlag) ACC_FINAL else 0,
      if (sym.isStaticMember) ACC_STATIC else 0,
      if (sym.isBridge) ACC_BRIDGE | ACC_SYNTHETIC else 0,
      if (sym.isHidden) ACC_SYNTHETIC else 0,
      if (sym.isClass && !sym.isInterface) ACC_SUPER else 0,
      if (sym.isVarargsMethod) ACC_VARARGS else 0,
      if (sym.hasFlag(Flags.SYNCHRONIZED)) ACC_SYNCHRONIZED else 0
    )
  }

  def javaFieldFlags(sym: Symbol) = {
    javaFlags(sym) | mkFlags(
      if (sym hasAnnotation TransientAttr) asm.Opcodes.ACC_TRANSIENT else 0,
      if (sym hasAnnotation VolatileAttr)  asm.Opcodes.ACC_VOLATILE  else 0,
      if (sym.isMutable) 0 else asm.Opcodes.ACC_FINAL
    )
  }

  def isTopLevelModule(sym: Symbol): Boolean =
    afterPickler { sym.isModuleClass && !sym.isImplClass && !sym.isNestedClass }

  def isStaticModule(sym: Symbol): Boolean = {
    sym.isModuleClass && !sym.isImplClass && !sym.isLifted
  }

  // -----------------------------------------------------------------------------------------
  // finding the least upper bound in agreement with the bytecode verifier (given two internal names handed by ASM)
  // Background:
  //  http://gallium.inria.fr/~xleroy/publi/bytecode-verification-JAR.pdf
  //  http://comments.gmane.org/gmane.comp.java.vm.languages/2293
  //  https://issues.scala-lang.org/browse/SI-3872
  // -----------------------------------------------------------------------------------------

  /**
   * Given an internal name (eg "java/lang/Integer") returns the class symbol for it.
   *
   * Better not to need this method (an example where control flow arrives here is welcome).
   * This method is invoked only upon both (1) and (2) below happening:
   *   (1) providing an asm.ClassWriter with an internal name by other means than javaName()
   *   (2) forgetting to track the corresponding class-symbol in reverseJavaName.
   *
   * (The first item is already unlikely because we rely on javaName()
   *  to do the bookkeeping for entries that should go in innerClassBuffer.)
   *
   * (We could do completely without this method at the expense of computing stack-map-frames ourselves and
   *  invoking visitFrame(), but that would require another pass over all instructions.)
   *
   * Right now I can't think of any invocation of visitSomething() on MethodVisitor
   * where we hand an internal name not backed by a reverseJavaName.
   * However, I'm leaving this note just in case any such oversight is discovered.
   */
  def inameToSymbol(iname: String): Symbol = {
    val name = global.newTypeName(iname)
    val res0 =
      if (nme.isModuleName(name)) rootMirror.getModule(nme.stripModuleSuffix(name))
      else                        rootMirror.getClassByName(name.replace('/', '.')) // TODO fails for inner classes (but this hasn't been tested).
    assert(res0 != NoSymbol, "inameToSymbol() returned NoSymbol.")
    val res = jsymbol(res0)
    res
  }

  def jsymbol(sym: Symbol): Symbol = {
    if(sym.isJavaDefined && sym.isModuleClass) sym.linkedClassOfClass
    else if(sym.isModule) sym.moduleClass
    else sym // we track only module-classes and plain-classes
  }

  def superClasses(s: Symbol): List[Symbol] = {
    assert(!s.isInterface)
    s.superClass match {
      case NoSymbol => List(s)
      case sc       => s :: superClasses(sc)
    }
  }

  def firstCommonSuffix(as: List[Symbol], bs: List[Symbol]): Symbol = {
    assert(!(as contains NoSymbol), "firstCommonSuffix() detected NoSymbol in " + as.toList.mkString)
    assert(!(bs contains NoSymbol), "firstCommonSuffix() detected NoSymbol in " + bs.toList.mkString)
    var chainA = as
    var chainB = bs
    var fcs: Symbol = NoSymbol
    do {
      if      (chainB contains chainA.head) fcs = chainA.head
      else if (chainA contains chainB.head) fcs = chainB.head
      else {
        chainA = chainA.tail
        chainB = chainB.tail
      }
    } while(fcs == NoSymbol)
    fcs
  }

  @inline final def jvmWiseLUB(a: Symbol, b: Symbol): Symbol = {

    assert(a.isClass, "jvmWiseLUB() received a non-class " + a.fullName)
    assert(b.isClass, "jvmWiseLUB() received a non-class " + b.fullName)

    val res = Pair(a.isInterface, b.isInterface) match {
      case (true, true) =>
        global.lub(List(a.tpe, b.tpe)).typeSymbol // TODO assert == firstCommonSuffix of resp. parents
      case (true, false) =>
        if(b isSubClass a) a else ObjectClass
      case (false, true) =>
        if(a isSubClass b) b else ObjectClass
      case _ =>
        firstCommonSuffix(superClasses(a), superClasses(b))
    }
    assert(res != NoSymbol, "jvmWiseLUB() returned NoSymbol.")
    res
  }

  /* The internal name of the least common ancestor of the types given by inameA and inameB.
     It's what ASM needs to know in order to compute stack map frames, http://asm.ow2.org/doc/developer-guide.html#controlflow */
  def getCommonSuperClass(inameA: String, inameB: String): String = {
    val a = reverseJavaName.getOrElseUpdate(inameA, inameToSymbol(inameA))
    val b = reverseJavaName.getOrElseUpdate(inameB, inameToSymbol(inameB))

    // global.lub(List(a.tpe, b.tpe)).typeSymbol.javaBinaryName.toString()
    // icodes.lub(icodes.toTypeKind(a.tpe), icodes.toTypeKind(b.tpe)).toType
    val lcaSym  = jvmWiseLUB(a, b)
    val lcaName = lcaSym.javaBinaryName.toString // don't call javaName because that side-effects innerClassBuffer.
    val oldsym  = reverseJavaName.put(lcaName, lcaSym)
    assert(oldsym.isEmpty || (oldsym.get == lcaSym), "somehow we're not managing to compute common-super-class for ASM consumption")
    assert(lcaName != "scala/Any")

    lcaName // TODO ASM caches the answer during the lifetime of a ClassWriter. We outlive that. Do some caching.
  }

  class CClassWriter(flags: Int) extends asm.ClassWriter(flags) {
    override def getCommonSuperClass(iname1: String, iname2: String): String = {
      BCodeUtils.this.getCommonSuperClass(iname1, iname2)
    }
  }

  // -----------------------------------------------------------------------------------------
  // constants
  // -----------------------------------------------------------------------------------------

  val classfileVersion: Int = settings.target.value match {
    case "jvm-1.5"     => asm.Opcodes.V1_5
    case "jvm-1.5-asm" => asm.Opcodes.V1_5
    case "jvm-1.6"     => asm.Opcodes.V1_6
    case "jvm-1.7"     => asm.Opcodes.V1_7
  }

  val majorVersion: Int = (classfileVersion & 0xFF)
  val emitStackMapFrame = (majorVersion >= 50)

  val extraProc: Int = mkFlags(
    asm.ClassWriter.COMPUTE_MAXS,
    if(emitStackMapFrame) asm.ClassWriter.COMPUTE_FRAMES else 0
  )

  val JAVA_LANG_OBJECT = asm.Type.getObjectType("java/lang/Object")
  val JAVA_LANG_STRING = asm.Type.getObjectType("java/lang/String")

  trait BCCommonPhase extends global.GlobalPhase {

    def isJavaEntryPoint(sym: Symbol, csymCompUnit: CompilationUnit) = {
      def fail(msg: String, pos: Position = sym.pos) = {
        csymCompUnit.warning(sym.pos,
          sym.name + " has a main method with parameter type Array[String], but " + sym.fullName('.') + " will not be a runnable program.\n" +
          "  Reason: " + msg
          // TODO: make this next claim true, if possible
          //   by generating valid main methods as static in module classes
          //   not sure what the jvm allows here
          // + "  You can still run the program by calling it as " + sym.javaSimpleName + " instead."
        )
        false
      }
      def failNoForwarder(msg: String) = {
        fail(msg + ", which means no static forwarder can be generated.\n")
      }
      val possibles = if (sym.hasModuleFlag) (sym.tpe nonPrivateMember nme.main).alternatives else Nil
      val hasApproximate = possibles exists { m =>
        m.info match {
          case MethodType(p :: Nil, _) => p.tpe.typeSymbol == ArrayClass
          case _                       => false
        }
      }
      // At this point it's a module with a main-looking method, so either succeed or warn that it isn't.
      hasApproximate && {
        // Before erasure so we can identify generic mains.
        beforeErasure {
          val companion     = sym.linkedClassOfClass
          val companionMain = companion.tpe.member(nme.main)

          if (hasJavaMainMethod(companion))
            failNoForwarder("companion contains its own main method")
          else if (companion.tpe.member(nme.main) != NoSymbol)
            // this is only because forwarders aren't smart enough yet
            failNoForwarder("companion contains its own main method (implementation restriction: no main is allowed, regardless of signature)")
          else if (companion.isTrait)
            failNoForwarder("companion is a trait")
          // Now either succeeed, or issue some additional warnings for things which look like
          // attempts to be java main methods.
          else possibles exists { m =>
            m.info match {
              case PolyType(_, _) =>
                fail("main methods cannot be generic.")
              case MethodType(params, res) =>
                if (res.typeSymbol :: params exists (_.isAbstractType))
                  fail("main methods cannot refer to type parameters or abstract types.", m.pos)
                else
                  isJavaMainMethod(m) || fail("main method must have exact signature (Array[String])Unit", m.pos)
              case tp =>
                fail("don't know what this is: " + tp, m.pos)
            }
          }
        }
      }
    }

    def initBytecodeWriter(entryPoints: List[Symbol]): BytecodeWriter = {
      settings.outputDirs.getSingleOutput match {
        case Some(f) if f hasExtension "jar" =>
          // If no main class was specified, see if there's only one
          // entry point among the classes going into the jar.
          if (settings.mainClass.isDefault) {
            entryPoints map (_.fullName('.')) match {
              case Nil      =>
                log("No Main-Class designated or discovered.")
              case name :: Nil =>
                log("Unique entry point: setting Main-Class to " + name)
                settings.mainClass.value = name
              case names =>
                log("No Main-Class due to multiple entry points:\n  " + names.mkString("\n  "))
            }
          }
          else log("Main-Class was specified: " + settings.mainClass.value)

          new DirectToJarfileWriter(f.file)

        case _                               =>
          if (settings.Ygenjavap.isDefault) {
            if(settings.Ydumpclasses.isDefault)
              new ClassBytecodeWriter { }
            else
              new ClassBytecodeWriter with DumpBytecodeWriter { }
          }
          else new ClassBytecodeWriter with JavapBytecodeWriter { }

          // TODO A ScalapBytecodeWriter could take asm.util.Textifier as starting point.
          //      Three areas where javap ouput is less than ideal (e.g. when comparing versions of the same classfile) are:
          //        (a) unreadable pickle;
          //        (b) two constant pools, while having identical contents, are displayed differently due to physical layout.
          //        (c) stack maps (classfile version 50 and up) are displayed in encoded form by javap, their expansion makes more sense instead.
      }
    }

  }

  /*
   * Custom attribute (JVMS 4.7.1) "ScalaSig" used as marker only
   * i.e., the pickle is contained in a custom annotation, see:
   *   (1) `addAnnotations()`,
   *   (2) SID # 10 (draft) - Storage of pickled Scala signatures in class files, http://www.scala-lang.org/sid/10
   *   (3) SID # 5 - Internals of Scala Annotations, http://www.scala-lang.org/sid/5
   * That annotation in turn is not related to the "java-generic-signature" (JVMS 4.7.9)
   * other than both ending up encoded as attributes (JVMS 4.7)
   * (with the caveat that the "ScalaSig" attribute is associated to some classes,
   * while the "Signature" attribute can be associated to classes, methods, and fields.)
   *
   **/
  trait BCPickles {

    import scala.reflect.internal.pickling.{ PickleFormat, PickleBuffer }

    val versionPickle = {
      val vp = new PickleBuffer(new Array[Byte](16), -1, 0)
      assert(vp.writeIndex == 0, vp)
      vp writeNat PickleFormat.MajorVersion
      vp writeNat PickleFormat.MinorVersion
      vp writeNat 0
      vp
    }

    def createJAttribute(name: String, b: Array[Byte], offset: Int, len: Int): asm.Attribute = {
      val dest = new Array[Byte](len);
      System.arraycopy(b, offset, dest, 0, len);
      new asm.CustomAttr(name, dest)
    }

    def pickleMarkerLocal = {
      createJAttribute(tpnme.ScalaSignatureATTR.toString, versionPickle.bytes, 0, versionPickle.writeIndex)
    }

    def pickleMarkerForeign = {
      createJAttribute(tpnme.ScalaATTR.toString, new Array[Byte](0), 0, 0)
    }

    /** Returns a ScalaSignature annotation if it must be added to this class, none otherwise.
     *  This annotation must be added to the class' annotations list when generating them.
     *
     *  Depending on whether the returned option is defined, it adds to `jclass` one of:
     *    (a) the ScalaSig marker attribute
     *        (indicating that a scala-signature-annotation aka pickle is present in this class); or
     *    (b) the Scala marker attribute
     *        (indicating that a scala-signature-annotation aka pickle is to be found in another file).
     *
     *
     *  @param jclassName The class file that is being readied.
     *  @param sym    The symbol for which the signature has been entered in the symData map.
     *                This is different than the symbol
     *                that is being generated in the case of a mirror class.
     *  @return       An option that is:
     *                - defined and contains an AnnotationInfo of the ScalaSignature type,
     *                  instantiated with the pickle signature for sym.
     *                - empty if the jclass/sym pair must not contain a pickle.
     *
     */
    def getAnnotPickle(jclassName: String, sym: Symbol): Option[AnnotationInfo] = {
      currentRun.symData get sym match {
        case Some(pickle) if !nme.isModuleName(newTermName(jclassName)) =>
          val scalaAnnot = {
            val sigBytes = ScalaSigBytes(pickle.bytes.take(pickle.writeIndex))
            AnnotationInfo(sigBytes.sigAnnot, Nil, List((nme.bytes, sigBytes)))
          }
          pickledBytes += pickle.writeIndex
          currentRun.symData -= sym
          currentRun.symData -= sym.companionSymbol
          Some(scalaAnnot)
        case _ =>
          None
      }
    }

  }

  trait BCInnerClassGen {

    val EMPTY_JTYPE_ARRAY  = Array.empty[asm.Type]
    val EMPTY_STRING_ARRAY = Array.empty[String]

    val mdesc_arglessvoid = "()V"

    val CLASS_CONSTRUCTOR_NAME    = "<clinit>"
    val INSTANCE_CONSTRUCTOR_NAME = "<init>"

    val INNER_CLASSES_FLAGS =
      (asm.Opcodes.ACC_PUBLIC    | asm.Opcodes.ACC_PRIVATE | asm.Opcodes.ACC_PROTECTED |
       asm.Opcodes.ACC_STATIC    | asm.Opcodes.ACC_INTERFACE | asm.Opcodes.ACC_ABSTRACT)

    val PublicStatic      = asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_STATIC
    val PublicStaticFinal = asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_STATIC | asm.Opcodes.ACC_FINAL

    val strMODULE_INSTANCE_FIELD = nme.MODULE_INSTANCE_FIELD.toString

    def debugLevel = settings.debuginfo.indexOfChoice

    val emitSource = debugLevel >= 1
    val emitLines  = debugLevel >= 2
    val emitVars   = debugLevel >= 3

    // -----------------------------------------------------------------------------------------
    // Getters for (JVMS 4.2) internal and unqualified names (represented as JType instances).
    // These getters track behind the scenes the inner classes referred to in the class being emitted,
    // so as to build the InnerClasses attribute (JVMS 4.7.6) via `addInnerClasses()`
    // (which also adds as member classes those inner classes that have been declared,
    // thus also covering the case of inner classes declared but otherwise not referred).
    // -----------------------------------------------------------------------------------------

    val innerClassBuffer = mutable.LinkedHashSet[Symbol]()

    /** For given symbol return a symbol corresponding to a class that should be declared as inner class.
     *
     *  For example:
     *  class A {
     *    class B
     *    object C
     *  }
     *
     *  then method will return:
     *    NoSymbol for A,
     *    the same symbol for A.B (corresponding to A$B class), and
     *    A$C$ symbol for A.C.
     */
    def innerClassSymbolFor(s: Symbol): Symbol =
      if (s.isClass) s else if (s.isModule) s.moduleClass else NoSymbol

    /** Return the a name of this symbol that can be used on the Java platform.  It removes spaces from names.
     *
     *  Special handling:
     *    scala.Nothing erases to scala.runtime.Nothing$
     *       scala.Null erases to scala.runtime.Null$
     *
     *  This is needed because they are not real classes, and they mean
     *  'abrupt termination upon evaluation of that expression' or null respectively.
     *  This handling is done already in GenICode, but here we need to remove
     *  references from method signatures to these types, because such classes
     *  cannot exist in the classpath: the type checker will be very confused.
     */
    def javaName(sym: Symbol): String = {

        /**
         * Checks if given symbol corresponds to inner class/object and add it to innerClassBuffer
         *
         * Note: This method is called recursively thus making sure that we add complete chain
         * of inner class all until root class.
         */
        def collectInnerClass(s: Symbol): Unit = {
          // TODO: some beforeFlatten { ... } which accounts for
          // being nested in parameterized classes (if we're going to selectively flatten.)
          val x = innerClassSymbolFor(s)
          if(x ne NoSymbol) {
            assert(x.isClass, "not an inner-class symbol")
            val isInner = !x.rawowner.isPackageClass
            if (isInner) {
              innerClassBuffer += x
              collectInnerClass(x.rawowner)
            }
          }
        }

      collectInnerClass(sym)

      var hasInternalName = (sym.isClass || (sym.isModule && !sym.isMethod))
      val cachedJN = javaNameCache.getOrElseUpdate(sym, {
        if (hasInternalName) { sym.javaBinaryName }
        else                 { sym.javaSimpleName }
      })

      if(emitStackMapFrame && hasInternalName) {
        val internalName = cachedJN.toString()
        val trackedSym = jsymbol(sym)
        reverseJavaName.get(internalName) match {
          case None         =>
            reverseJavaName.put(internalName, trackedSym)
          case Some(oldsym) =>
            assert((oldsym == trackedSym) || (oldsym == RuntimeNothingClass) || (oldsym == RuntimeNullClass), // In contrast, neither NothingClass nor NullClass show up bytecode-level.
                   "how can getCommonSuperclass() do its job if different class symbols get the same bytecode-level internal name.")
        }
      }

      cachedJN.toString
    }

    /** Specialized array conversion to prevent calling
     *  java.lang.reflect.Array.newInstance via TraversableOnce.toArray
     */
    def mkArray(xs: Traversable[asm.Type]):  Array[asm.Type]  = { val a = new Array[asm.Type](xs.size); xs.copyToArray(a); a }
    def mkArray(xs: Traversable[String]):    Array[String]    = { val a = new Array[String](xs.size);   xs.copyToArray(a); a }

    def descriptor(t: Type):     String = { javaType(t).getDescriptor }
    def descriptor(k: TypeKind): String = { javaType(k).getDescriptor }
    def descriptor(s: Symbol):   String = { javaType(s).getDescriptor }

    def javaType(tk: TypeKind): asm.Type = {
      if(tk.isValueType) {
        if(tk.isIntSizedType) {
          (tk: @unchecked) match {
            case BOOL   => asm.Type.BOOLEAN_TYPE
            case BYTE   => asm.Type.BYTE_TYPE
            case SHORT  => asm.Type.SHORT_TYPE
            case CHAR   => asm.Type.CHAR_TYPE
            case INT    => asm.Type.INT_TYPE
          }
        } else {
          (tk: @unchecked) match {
            case UNIT   => asm.Type.VOID_TYPE
            case LONG   => asm.Type.LONG_TYPE
            case FLOAT  => asm.Type.FLOAT_TYPE
            case DOUBLE => asm.Type.DOUBLE_TYPE
          }
        }
      } else {
        assert(!tk.isBoxedType, tk) // documentation (BOXED matches none below anyway)
        (tk: @unchecked) match {
          case REFERENCE(cls)  => asm.Type.getObjectType(javaName(cls))
          case ARRAY(elem)     => javaArrayType(javaType(elem))
        }
      }
    }

    def javaType(t: Type): asm.Type = javaType(toTypeKind(t))

    def javaType(s: Symbol): asm.Type = {
      if (s.isMethod) {
        val resT: asm.Type = if (s.isClassConstructor) asm.Type.VOID_TYPE else javaType(s.tpe.resultType);
        asm.Type.getMethodType( resT, (s.tpe.paramTypes map javaType): _* )
      } else { javaType(s.tpe) }
    }

    def javaArrayType(elem: asm.Type): asm.Type = { asm.Type.getObjectType("[" + elem.getDescriptor) }

    def isDeprecated(sym: Symbol): Boolean = { sym.annotations exists (_ matches definitions.DeprecatedAttr) }

    def addInnerClasses(csym: Symbol, jclass: asm.ClassVisitor) {
      /** The outer name for this inner class. Note that it returns null
       *  when the inner class should not get an index in the constant pool.
       *  That means non-member classes (anonymous). See Section 4.7.5 in the JVMS.
       */
      def outerName(innerSym: Symbol): String = {
        if (innerSym.originalEnclosingMethod != NoSymbol)
          null
        else {
          val outerName = javaName(innerSym.rawowner)
          if (isTopLevelModule(innerSym.rawowner)) "" + nme.stripModuleSuffix(newTermName(outerName))
          else outerName
        }
      }

      def innerName(innerSym: Symbol): String =
        if (innerSym.isAnonymousClass || innerSym.isAnonymousFunction)
          null
        else
          innerSym.rawname + innerSym.moduleSuffix

      // add inner classes which might not have been referenced yet
      afterErasure {
        for (sym <- List(csym, csym.linkedClassOfClass); m <- sym.info.decls.map(innerClassSymbolFor) if m.isClass)
          innerClassBuffer += m
      }

      val allInners: List[Symbol] = innerClassBuffer.toList
      if (allInners.nonEmpty) {
        debuglog(csym.fullName('.') + " contains " + allInners.size + " inner classes.")

        // entries ready to be serialized into the classfile, used to detect duplicates.
        val entries = mutable.Map.empty[String, String]

        // sort them so inner classes succeed their enclosing class to satisfy the Eclipse Java compiler
        for (innerSym <- allInners sortBy (_.name.length)) { // TODO why not sortBy (_.name.toString()) ??
          val flags = mkFlags(
            if (innerSym.rawowner.hasModuleFlag) asm.Opcodes.ACC_STATIC else 0,
            javaFlags(innerSym),
            if(isDeprecated(innerSym)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo-access flag
          ) & (INNER_CLASSES_FLAGS | asm.Opcodes.ACC_DEPRECATED)
          val jname = javaName(innerSym)  // never null
          val oname = outerName(innerSym) // null when method-enclosed
          val iname = innerName(innerSym) // null for anonymous inner class

          // Mimicking javap inner class output
          debuglog(
            if (oname == null || iname == null) "//class " + jname
            else "//%s=class %s of class %s".format(iname, jname, oname)
          )

          assert(jname != null, "javaName is broken.") // documentation
          val doAdd = entries.get(jname) match {
            // TODO is it ok for prevOName to be null? (Someone should really document the invariants of the InnerClasses bytecode attribute)
            case Some(prevOName) =>
              // this occurs e.g. when innerClassBuffer contains both class Thread$State, object Thread$State,
              // i.e. for them it must be the case that oname == java/lang/Thread
              assert(prevOName == oname, "duplicate")
              false
            case None => true
          }

          if(doAdd) {
            entries += (jname -> oname)
            jclass.visitInnerClass(jname, oname, iname, flags)
          }

          /*
           * TODO assert (JVMS 4.7.6 The InnerClasses attribute)
           * If a class file has a version number that is greater than or equal to 51.0, and
           * has an InnerClasses attribute in its attributes table, then for all entries in the
           * classes array of the InnerClasses attribute, the value of the
           * outer_class_info_index item must be zero if the value of the
           * inner_name_index item is zero.
           */

        }
      }
    }


    /** Just a namespace for utilities that encapsulate MethodVisitor idioms.
     *  In the ASM world, org.objectweb.asm.commons.InstructionAdapter plays a similar role,
     *  but the methods here allow choosing when to transition from ICode to ASM types
     *  (including not at all, e.g. for performance).
     */
    abstract class JCodeMethodV {

      def jmethod: asm.MethodVisitor

      import asm.Opcodes;

      def aconst(cst: AnyRef) {
        if (cst == null) { jmethod.visitInsn(Opcodes.ACONST_NULL) }
        else             { jmethod.visitLdcInsn(cst) }
      }

      @inline final def boolconst(b: Boolean) { iconst(if(b) 1 else 0) }

      def iconst(cst: Int) {
        if (cst >= -1 && cst <= 5) {
          jmethod.visitInsn(Opcodes.ICONST_0 + cst)
        } else if (cst >= java.lang.Byte.MIN_VALUE && cst <= java.lang.Byte.MAX_VALUE) {
          jmethod.visitIntInsn(Opcodes.BIPUSH, cst)
        } else if (cst >= java.lang.Short.MIN_VALUE && cst <= java.lang.Short.MAX_VALUE) {
          jmethod.visitIntInsn(Opcodes.SIPUSH, cst)
        } else {
          jmethod.visitLdcInsn(new Integer(cst))
        }
      }

      def lconst(cst: Long) {
        if (cst == 0L || cst == 1L) {
          jmethod.visitInsn(Opcodes.LCONST_0 + cst.asInstanceOf[Int])
        } else {
          jmethod.visitLdcInsn(new java.lang.Long(cst))
        }
      }

      def fconst(cst: Float) {
        val bits: Int = java.lang.Float.floatToIntBits(cst)
        if (bits == 0L || bits == 0x3f800000 || bits == 0x40000000) { // 0..2
          jmethod.visitInsn(Opcodes.FCONST_0 + cst.asInstanceOf[Int])
        } else {
          jmethod.visitLdcInsn(new java.lang.Float(cst))
        }
      }

      def dconst(cst: Double) {
        val bits: Long = java.lang.Double.doubleToLongBits(cst)
        if (bits == 0L || bits == 0x3ff0000000000000L) { // +0.0d and 1.0d
          jmethod.visitInsn(Opcodes.DCONST_0 + cst.asInstanceOf[Int])
        } else {
          jmethod.visitLdcInsn(new java.lang.Double(cst))
        }
      }

      def newarray(elem: TypeKind) {
        if(elem.isRefOrArrayType) {
          jmethod.visitTypeInsn(Opcodes.ANEWARRAY, javaType(elem).getInternalName)
        } else {
          val rand = {
            if(elem.isIntSizedType) {
              (elem: @unchecked) match {
                case BOOL   => Opcodes.T_BOOLEAN
                case BYTE   => Opcodes.T_BYTE
                case SHORT  => Opcodes.T_SHORT
                case CHAR   => Opcodes.T_CHAR
                case INT    => Opcodes.T_INT
              }
            } else {
              (elem: @unchecked) match {
                case LONG   => Opcodes.T_LONG
                case FLOAT  => Opcodes.T_FLOAT
                case DOUBLE => Opcodes.T_DOUBLE
              }
            }
          }
          jmethod.visitIntInsn(Opcodes.NEWARRAY, rand)
        }
      }


      @inline def load( idx: Int, tk: TypeKind) { emitVarInsn(Opcodes.ILOAD,  idx, tk) }
      @inline def store(idx: Int, tk: TypeKind) { emitVarInsn(Opcodes.ISTORE, idx, tk) }

      @inline def aload( tk: TypeKind) { emitTypeBased(aloadOpcodes,  tk) }
      @inline def astore(tk: TypeKind) { emitTypeBased(astoreOpcodes, tk) }

      @inline def neg(tk: TypeKind) { emitPrimitive(negOpcodes, tk) }
      @inline def add(tk: TypeKind) { emitPrimitive(addOpcodes, tk) }
      @inline def sub(tk: TypeKind) { emitPrimitive(subOpcodes, tk) }
      @inline def mul(tk: TypeKind) { emitPrimitive(mulOpcodes, tk) }
      @inline def div(tk: TypeKind) { emitPrimitive(divOpcodes, tk) }
      @inline def rem(tk: TypeKind) { emitPrimitive(remOpcodes, tk) }

      @inline def invokespecial(owner: String, name: String, desc: String) {
        jmethod.visitMethodInsn(Opcodes.INVOKESPECIAL, owner, name, desc)
      }
      @inline def invokestatic(owner: String, name: String, desc: String) {
        jmethod.visitMethodInsn(Opcodes.INVOKESTATIC, owner, name, desc)
      }
      @inline def invokeinterface(owner: String, name: String, desc: String) {
        jmethod.visitMethodInsn(Opcodes.INVOKEINTERFACE, owner, name, desc)
      }
      @inline def invokevirtual(owner: String, name: String, desc: String) {
        jmethod.visitMethodInsn(Opcodes.INVOKEVIRTUAL, owner, name, desc)
      }

      @inline def goTo(label: asm.Label) { jmethod.visitJumpInsn(Opcodes.GOTO, label) }
      @inline def emitIF(cond: TestOp, label: asm.Label)      { jmethod.visitJumpInsn(cond.opcodeIF,     label) }
      @inline def emitIF_ICMP(cond: TestOp, label: asm.Label) { jmethod.visitJumpInsn(cond.opcodeIFICMP, label) }
      @inline def emitIF_ACMP(cond: TestOp, label: asm.Label) {
        assert((cond == EQ) || (cond == NE), cond)
        val opc = (if(cond == EQ) Opcodes.IF_ACMPEQ else Opcodes.IF_ACMPNE)
        jmethod.visitJumpInsn(opc, label)
      }
      @inline def emitIFNONNULL(label: asm.Label) { jmethod.visitJumpInsn(Opcodes.IFNONNULL, label) }
      @inline def emitIFNULL   (label: asm.Label) { jmethod.visitJumpInsn(Opcodes.IFNULL,    label) }

      @inline def emitRETURN(tk: TypeKind) {
        if(tk == UNIT) { jmethod.visitInsn(Opcodes.RETURN) }
        else           { emitTypeBased(returnOpcodes, tk)      }
      }

      /** Emits one of tableswitch or lookoupswitch. */
      def emitSWITCH(keys: Array[Int], branches: Array[asm.Label], defaultBranch: asm.Label, minDensity: Double) {
        assert(keys.length == branches.length)

        // For empty keys, it makes sense emitting LOOKUPSWITCH with defaultBranch only.
        // Similar to what javac emits for a switch statement consisting only of a default case.
        if (keys.length == 0) {
          jmethod.visitLookupSwitchInsn(defaultBranch, keys, branches)
          return
        }

        // sort `keys` by increasing key, keeping `branches` in sync. TODO FIXME use quicksort
        var i = 1
        while (i < keys.length) {
          var j = 1
          while (j <= keys.length - i) {
            if (keys(j) < keys(j - 1)) {
              val tmp     = keys(j)
              keys(j)     = keys(j - 1)
              keys(j - 1) = tmp
              val tmpL        = branches(j)
              branches(j)     = branches(j - 1)
              branches(j - 1) = tmpL
            }
            j += 1
          }
          i += 1
        }

        // check for duplicate keys to avoid "VerifyError: unsorted lookupswitch" (SI-6011)
        i = 1
        while (i < keys.length) {
          if(keys(i-1) == keys(i)) {
            abort("duplicate keys in SWITCH, can't pick arbitrarily one of them to evict, see SI-6011.")
          }
          i += 1
        }

        val keyMin = keys(0)
        val keyMax = keys(keys.length - 1)

        val isDenseEnough: Boolean = {
          /** Calculate in long to guard against overflow. TODO what overflow??? */
          val keyRangeD: Double = (keyMax.asInstanceOf[Long] - keyMin + 1).asInstanceOf[Double]
          val klenD:     Double = keys.length
          val kdensity:  Double = (klenD / keyRangeD)

          kdensity >= minDensity
        }

        if (isDenseEnough) {
          // use a table in which holes are filled with defaultBranch.
          val keyRange    = (keyMax - keyMin + 1)
          val newBranches = new Array[asm.Label](keyRange)
          var oldPos = 0;
          var i = 0
          while(i < keyRange) {
            val key = keyMin + i;
            if (keys(oldPos) == key) {
              newBranches(i) = branches(oldPos)
              oldPos += 1
            } else {
              newBranches(i) = defaultBranch
            }
            i += 1
          }
          assert(oldPos == keys.length, "emitSWITCH")
          jmethod.visitTableSwitchInsn(keyMin, keyMax, defaultBranch, newBranches: _*)
        } else {
          jmethod.visitLookupSwitchInsn(defaultBranch, keys, branches)
        }
      }

      // internal helpers -- not part of the public API of `jcode`
      // don't make private otherwise inlining will suffer

      def emitVarInsn(opc: Int, idx: Int, tk: TypeKind) {
        assert((opc == Opcodes.ILOAD) || (opc == Opcodes.ISTORE), opc)
        jmethod.visitVarInsn(javaType(tk).getOpcode(opc), idx)
      }

      // ---------------- array load and store ----------------

      val aloadOpcodes  = { import Opcodes._; Array(AALOAD,  BALOAD,  SALOAD,  CALOAD,  IALOAD,  LALOAD,  FALOAD,  DALOAD)  }
      val astoreOpcodes = { import Opcodes._; Array(AASTORE, BASTORE, SASTORE, CASTORE, IASTORE, LASTORE, FASTORE, DASTORE) }

      val returnOpcodes = { import Opcodes._; Array(ARETURN, IRETURN, IRETURN, IRETURN, IRETURN, LRETURN, FRETURN, DRETURN) }

      def emitTypeBased(opcs: Array[Int], tk: TypeKind) {
        assert(tk != UNIT, tk)
        val opc = {
          if(tk.isRefOrArrayType) {   opcs(0) }
          else if(tk.isIntSizedType) {
            (tk: @unchecked) match {
              case BOOL | BYTE     => opcs(1)
              case SHORT           => opcs(2)
              case CHAR            => opcs(3)
              case INT             => opcs(4)
            }
          } else {
            (tk: @unchecked) match {
              case LONG            => opcs(5)
              case FLOAT           => opcs(6)
              case DOUBLE          => opcs(7)
            }
          }
        }
        jmethod.visitInsn(opc)
      }

      // ---------------- primitive operations ----------------

      val negOpcodes: Array[Int] = { import Opcodes._; Array(INEG, LNEG, FNEG, DNEG) }
      val addOpcodes: Array[Int] = { import Opcodes._; Array(IADD, LADD, FADD, DADD) }
      val subOpcodes: Array[Int] = { import Opcodes._; Array(ISUB, LSUB, FSUB, DSUB) }
      val mulOpcodes: Array[Int] = { import Opcodes._; Array(IMUL, LMUL, FMUL, DMUL) }
      val divOpcodes: Array[Int] = { import Opcodes._; Array(IDIV, LDIV, FDIV, DDIV) }
      val remOpcodes: Array[Int] = { import Opcodes._; Array(IREM, LREM, FREM, DREM) }

      def emitPrimitive(opcs: Array[Int], tk: TypeKind) {
        val opc = {
          if(tk.isIntSizedType) { opcs(0) }
          else {
            (tk: @unchecked) match {
              case LONG   => opcs(1)
              case FLOAT  => opcs(2)
              case DOUBLE => opcs(3)
            }
          }
        }
        jmethod.visitInsn(opc)
      }

    } // end of class JCodeMethodV

    abstract class JCodeMethodN extends JCodeMethodV {
      override def jmethod: asm.tree.MethodNode
    }

  } // end of trait BCInnerClassGen

  trait BCAnnotGen extends BCInnerClassGen {

    def ubytesToCharArray(bytes: Array[Byte]): Array[Char] = {
      val ca = new Array[Char](bytes.size)
      var idx = 0
      while(idx < bytes.size) {
        val b: Byte = bytes(idx)
        assert((b & ~0x7f) == 0)
        ca(idx) = b.asInstanceOf[Char]
        idx += 1
      }

      ca
    }

    // TODO this method isn't exercised during bootstrapping. Open question: is it bug free?
    private def arrEncode(sb: ScalaSigBytes): Array[String] = {
      var strs: List[String]  = Nil
      val bSeven: Array[Byte] = sb.sevenBitsMayBeZero
      // chop into slices of at most 65535 bytes, counting 0x00 as taking two bytes (as per JVMS 4.4.7 The CONSTANT_Utf8_info Structure)
      var prevOffset = 0
      var offset     = 0
      var encLength  = 0
      while(offset < bSeven.size) {
        val newEncLength = encLength.toLong + (if(bSeven(offset) == 0) 2 else 1)
        if(newEncLength > 65535) {
          val ba     = bSeven.slice(prevOffset, offset)
          strs     ::= new java.lang.String(ubytesToCharArray(ba))
          encLength  = 0
          prevOffset = offset
        } else {
          encLength += 1
          offset    += 1
        }
      }
      if(prevOffset < offset) {
        assert(offset == bSeven.length)
        val ba = bSeven.slice(prevOffset, offset)
        strs ::= new java.lang.String(ubytesToCharArray(ba))
      }
      assert(strs.size > 1, "encode instead as one String via strEncode()") // TODO too strict?
      strs.reverse.toArray
    }

    private def strEncode(sb: ScalaSigBytes): String = {
      val ca = ubytesToCharArray(sb.sevenBitsMayBeZero)
      new java.lang.String(ca)
      // debug val bvA = new asm.ByteVector; bvA.putUTF8(s)
      // debug val enc: Array[Byte] = scala.reflect.internal.pickling.ByteCodecs.encode(bytes)
      // debug assert(enc(idx) == bvA.getByte(idx + 2))
      // debug assert(bvA.getLength == enc.size + 2)
    }

    def emitArgument(av:   asm.AnnotationVisitor,
                     name: String,
                     arg:  ClassfileAnnotArg) {
      arg match {

        case LiteralAnnotArg(const) =>
          if(const.isNonUnitAnyVal) { av.visit(name, const.value) }
          else {
            const.tag match {
              case StringTag  =>
                assert(const.value != null, const) // TODO this invariant isn't documented in `case class Constant`
                av.visit(name, const.stringValue)  // `stringValue` special-cases null, but that execution path isn't exercised for a const with StringTag
              case ClazzTag   => av.visit(name, javaType(const.typeValue))
              case EnumTag =>
                val edesc  = descriptor(const.tpe) // the class descriptor of the enumeration class.
                val evalue = const.symbolValue.name.toString // value the actual enumeration value.
                av.visitEnum(name, edesc, evalue)
            }
          }

        case sb@ScalaSigBytes(bytes) =>
          // see http://www.scala-lang.org/sid/10 (Storage of pickled Scala signatures in class files)
          // also JVMS Sec. 4.7.16.1 The element_value structure and JVMS Sec. 4.4.7 The CONSTANT_Utf8_info Structure.
          val assocValue = (if(sb.fitsInOneString) strEncode(sb) else arrEncode(sb))
          av.visit(name, assocValue)
          // for the lazy val in ScalaSigBytes to be GC'ed, the invoker of emitAnnotations() should hold the ScalaSigBytes in a method-local var that doesn't escape.

        case ArrayAnnotArg(args) =>
          val arrAnnotV: asm.AnnotationVisitor = av.visitArray(name)
          for(arg <- args) { emitArgument(arrAnnotV, null, arg) }
          arrAnnotV.visitEnd()

        case NestedAnnotArg(annInfo) =>
          val AnnotationInfo(typ, args, assocs) = annInfo
          assert(args.isEmpty, args)
          val desc = descriptor(typ) // the class descriptor of the nested annotation class
          val nestedVisitor = av.visitAnnotation(name, desc)
          emitAssocs(nestedVisitor, assocs)
      }
    }

    /** Whether an annotation should be emitted as a Java annotation
     *   .initialize: if 'annot' is read from pickle, atp might be un-initialized
     */
    private def shouldEmitAnnotation(annot: AnnotationInfo) =
      annot.symbol.initialize.isJavaDefined &&
      annot.matches(ClassfileAnnotationClass) &&
      annot.args.isEmpty &&
      !annot.matches(DeprecatedAttr)

    def emitAssocs(av: asm.AnnotationVisitor, assocs: List[(Name, ClassfileAnnotArg)]) {
      for ((name, value) <- assocs) {
        emitArgument(av, name.toString(), value)
      }
      av.visitEnd()
    }

    def emitAnnotations(cw: asm.ClassVisitor, annotations: List[AnnotationInfo]) {
      for(annot <- annotations; if shouldEmitAnnotation(annot)) {
        val AnnotationInfo(typ, args, assocs) = annot
        assert(args.isEmpty, args)
        val av = cw.visitAnnotation(descriptor(typ), true)
        emitAssocs(av, assocs)
      }
    }

    def emitAnnotations(mw: asm.MethodVisitor, annotations: List[AnnotationInfo]) {
      for(annot <- annotations; if shouldEmitAnnotation(annot)) {
        val AnnotationInfo(typ, args, assocs) = annot
        assert(args.isEmpty, args)
        val av = mw.visitAnnotation(descriptor(typ), true)
        emitAssocs(av, assocs)
      }
    }

    def emitAnnotations(fw: asm.FieldVisitor, annotations: List[AnnotationInfo]) {
      for(annot <- annotations; if shouldEmitAnnotation(annot)) {
        val AnnotationInfo(typ, args, assocs) = annot
        assert(args.isEmpty, args)
        val av = fw.visitAnnotation(descriptor(typ), true)
        emitAssocs(av, assocs)
      }
    }

    def emitParamAnnotations(jmethod: asm.MethodVisitor, pannotss: List[List[AnnotationInfo]]) {
      val annotationss = pannotss map (_ filter shouldEmitAnnotation)
      if (annotationss forall (_.isEmpty)) return
      for (Pair(annots, idx) <- annotationss.zipWithIndex;
           annot <- annots) {
        val AnnotationInfo(typ, args, assocs) = annot
        assert(args.isEmpty, args)
        val pannVisitor: asm.AnnotationVisitor = jmethod.visitParameterAnnotation(idx, descriptor(typ), true)
        emitAssocs(pannVisitor, assocs)
      }
    }

  } // end of trait BCAnnotGen

  trait BCJGenSigGen {

    // @M don't generate java generics sigs for (members of) implementation
    // classes, as they are monomorphic (TODO: ok?)
    private def needsGenericSignature(sym: Symbol) = !(
      // PP: This condition used to include sym.hasExpandedName, but this leads
      // to the total loss of generic information if a private member is
      // accessed from a closure: both the field and the accessor were generated
      // without it.  This is particularly bad because the availability of
      // generic information could disappear as a consequence of a seemingly
      // unrelated change.
         settings.Ynogenericsig.value
      || sym.isHidden
      || sym.isLiftedMethod
      || sym.isBridge
      || (sym.ownerChain exists (_.isImplClass))
    )

    def getCurrentCUnit(): CompilationUnit

    /** @return
     *   - `null` if no Java signature is to be added (`null` is what ASM expects in these cases).
     *   - otherwise the signature in question
     */
    def getGenericSignature(sym: Symbol, owner: Symbol): String = {

      if (!needsGenericSignature(sym)) { return null }

      val memberTpe = beforeErasure(owner.thisType.memberInfo(sym))

      val jsOpt: Option[String] = erasure.javaSig(sym, memberTpe)
      if (jsOpt.isEmpty) { return null }

      val sig = jsOpt.get
      log(sig) // This seems useful enough in the general case.

          def wrap(op: => Unit) = {
            try   { op; true }
            catch { case _ : Throwable => false }
          }

      if (settings.Xverify.value) {
        // Run the signature parser to catch bogus signatures.
        val isValidSignature = wrap {
          // Alternative: scala.tools.reflect.SigParser (frontend to sun.reflect.generics.parser.SignatureParser)
          import scala.tools.asm.util.SignatureChecker
          if (sym.isMethod)    { SignatureChecker checkMethodSignature sig } // requires asm-util.jar
          else if (sym.isTerm) { SignatureChecker checkFieldSignature  sig }
          else                 { SignatureChecker checkClassSignature  sig }
        }

        if(!isValidSignature) {
          getCurrentCUnit().warning(sym.pos,
              """|compiler bug: created invalid generic signature for %s in %s
                 |signature: %s
                 |if this is reproducible, please report bug at https://issues.scala-lang.org/
              """.trim.stripMargin.format(sym, sym.owner.skipPackageObject.fullName, sig))
          return null
        }
      }

      if ((settings.check containsName phaseName)) {
        val normalizedTpe = beforeErasure(erasure.prepareSigMap(memberTpe))
        val bytecodeTpe = owner.thisType.memberInfo(sym)
        if (!sym.isType && !sym.isConstructor && !(erasure.erasure(sym)(normalizedTpe) =:= bytecodeTpe)) {
          getCurrentCUnit().warning(sym.pos,
              """|compiler bug: created generic signature for %s in %s that does not conform to its erasure
                 |signature: %s
                 |original type: %s
                 |normalized type: %s
                 |erasure type: %s
                 |if this is reproducible, please report bug at http://issues.scala-lang.org/
              """.trim.stripMargin.format(sym, sym.owner.skipPackageObject.fullName, sig, memberTpe, normalizedTpe, bytecodeTpe))
           return null
        }
      }

      sig
    }

  } // end of trait BCJGenSigGen

  trait BCForwardersGen extends BCAnnotGen with BCJGenSigGen {

    // -----------------------------------------------------------------------------------------
    // Static forwarders (related to mirror classes but also present in
    // a plain class lacking companion module, for details see `isCandidateForForwarders`).
    // -----------------------------------------------------------------------------------------

    val ExcludedForwarderFlags = {
      import Flags._
      // Should include DEFERRED but this breaks findMember.
      ( CASE | SPECIALIZED | LIFTED | PROTECTED | STATIC | EXPANDEDNAME | BridgeAndPrivateFlags )
    }

    /** Adds a @remote annotation, actual use unknown.
     *
     * Invoked from genMethod() and addForwarder().
     */
    def addRemoteExceptionAnnot(isRemoteClass: Boolean, isJMethodPublic: Boolean, meth: Symbol) {
      val needsAnnotation = (
        (  isRemoteClass ||
           isRemote(meth) && isJMethodPublic
        ) && !(meth.throwsAnnotations contains RemoteExceptionClass)
      )
      if (needsAnnotation) {
        val c   = Constant(RemoteExceptionClass.tpe)
        val arg = Literal(c) setType c.tpe
        meth.addAnnotation(ThrowsClass, arg)
      }
    }

    /** Add a forwarder for method m. Used only from addForwarders(). */
    private def addForwarder(isRemoteClass: Boolean, jclass: asm.ClassVisitor, module: Symbol, m: Symbol) {
      val moduleName     = javaName(module)
      val methodInfo     = module.thisType.memberInfo(m)
      val paramJavaTypes: List[asm.Type] = methodInfo.paramTypes map javaType
      // val paramNames     = 0 until paramJavaTypes.length map ("x_" + _)

      /** Forwarders must not be marked final,
       *  as the JVM will not allow redefinition of a final static method,
       *  and we don't know what classes might be subclassing the companion class.  See SI-4827.
       */
      // TODO: evaluate the other flags we might be dropping on the floor here.
      // TODO: ACC_SYNTHETIC ?
      val flags = PublicStatic | (
        if (m.isVarargsMethod) asm.Opcodes.ACC_VARARGS else 0
      )

      // TODO needed? for(ann <- m.annotations) { ann.symbol.initialize }
      val jgensig = if (m.isDeferred) null else getGenericSignature(m, module); // only add generic signature if method concrete; bug #1745
      addRemoteExceptionAnnot(isRemoteClass, hasPublicBitSet(flags), m)
      val (throws, others) = m.annotations partition (_.symbol == ThrowsClass)
      val thrownExceptions: List[String] = getExceptions(throws)

      val jReturnType = javaType(methodInfo.resultType)
      val mdesc = asm.Type.getMethodDescriptor(jReturnType, paramJavaTypes: _*)
      val mirrorMethodName = javaName(m)
      val mirrorMethod: asm.MethodVisitor = jclass.visitMethod(
        flags,
        mirrorMethodName,
        mdesc,
        jgensig,
        mkArray(thrownExceptions)
      )

      // typestate: entering mode with valid call sequences:
      //   [ visitAnnotationDefault ] ( visitAnnotation | visitParameterAnnotation | visitAttribute )*

      emitAnnotations(mirrorMethod, others)
      emitParamAnnotations(mirrorMethod, m.info.params.map(_.annotations))

      // typestate: entering mode with valid call sequences:
      //   visitCode ( visitFrame | visitXInsn | visitLabel | visitTryCatchBlock | visitLocalVariable | visitLineNumber )* visitMaxs ] visitEnd

      mirrorMethod.visitCode()

      mirrorMethod.visitFieldInsn(asm.Opcodes.GETSTATIC, moduleName, strMODULE_INSTANCE_FIELD, descriptor(module))

      var index = 0
      for(jparamType <- paramJavaTypes) {
        mirrorMethod.visitVarInsn(jparamType.getOpcode(asm.Opcodes.ILOAD), index)
        assert(jparamType.getSort() != asm.Type.METHOD, jparamType)
        index += jparamType.getSize()
      }

      mirrorMethod.visitMethodInsn(asm.Opcodes.INVOKEVIRTUAL, moduleName, mirrorMethodName, javaType(m).getDescriptor)
      mirrorMethod.visitInsn(jReturnType.getOpcode(asm.Opcodes.IRETURN))

      mirrorMethod.visitMaxs(0, 0) // just to follow protocol, dummy arguments
      mirrorMethod.visitEnd()

    }

    /** Add forwarders for all methods defined in `module` that don't conflict
     *  with methods in the companion class of `module`. A conflict arises when
     *  a method with the same name is defined both in a class and its companion object:
     *  method signature is not taken into account.
     */
    def addForwarders(isRemoteClass: Boolean, jclass: asm.ClassVisitor, jclassName: String, moduleClass: Symbol) {
      assert(moduleClass.isModuleClass, moduleClass)
      debuglog("Dumping mirror class for object: " + moduleClass)

      val linkedClass  = moduleClass.companionClass
      val linkedModule = linkedClass.companionSymbol
      lazy val conflictingNames: Set[Name] = {
        linkedClass.info.members collect { case sym if sym.name.isTermName => sym.name } toSet
      }
      debuglog("Potentially conflicting names for forwarders: " + conflictingNames)

      for (m <- moduleClass.info.membersBasedOnFlags(ExcludedForwarderFlags, Flags.METHOD)) {
        if (m.isType || m.isDeferred || (m.owner eq ObjectClass) || m.isConstructor)
          debuglog("No forwarder for '%s' from %s to '%s'".format(m, jclassName, moduleClass))
        else if (conflictingNames(m.name))
          log("No forwarder for " + m + " due to conflict with " + linkedClass.info.member(m.name))
        else {
          log("Adding static forwarder for '%s' from %s to '%s'".format(m, jclassName, moduleClass))
          addForwarder(isRemoteClass, jclass, moduleClass, m)
        }
      }
    }

    /**
     * Quoting from JVMS 4.7.5 The Exceptions Attribute
     *   "The Exceptions attribute indicates which checked exceptions a method may throw.
     *    There may be at most one Exceptions attribute in each method_info structure."
     *
     * The contents of that attribute are determined by the `String[] exceptions` argument to ASM's ClassVisitor.visitMethod()
     * This method returns such list of internal names.
     *
     */
    def getExceptions(excs: List[AnnotationInfo]): List[String] = {
      for (AnnotationInfo(tp, List(exc), _) <- excs.distinct if tp.typeSymbol == ThrowsClass)
      yield {
        val Literal(const) = exc
        javaName(const.typeValue.typeSymbol)
      }
    }

  } // end of trait BCForwardersGen

  trait BCClassGen extends BCInnerClassGen {

    /**
     * @param owner internal name of the enclosing class of the class.
     *
     * @param name the name of the method that contains the class.

     * @param methodType the method that contains the class.
     */
    case class EnclMethodEntry(owner: String, name: String, methodType: asm.Type)

    /**
     * @return null if the current class is not internal to a method
     *
     * Quoting from JVMS 4.7.7 The EnclosingMethod Attribute
     *   A class must have an EnclosingMethod attribute if and only if it is a local class or an anonymous class.
     *   A class may have no more than one EnclosingMethod attribute.
     *
     */
    def getEnclosingMethodAttribute(clazz: Symbol): EnclMethodEntry = { // JVMS 4.7.7
      var res: EnclMethodEntry = null
      val sym = clazz.originalEnclosingMethod
      if (sym.isMethod) {
        debuglog("enclosing method for %s is %s (in %s)".format(clazz, sym, sym.enclClass))
        res = EnclMethodEntry(javaName(sym.enclClass), javaName(sym), javaType(sym))
      } else if (clazz.isAnonymousClass) {
        val enclClass = clazz.rawowner
        assert(enclClass.isClass, enclClass)
        val sym = enclClass.primaryConstructor
        if (sym == NoSymbol) {
          log("Ran out of room looking for an enclosing method for %s: no constructor here.".format(enclClass, clazz))
        } else {
          debuglog("enclosing method for %s is %s (in %s)".format(clazz, sym, enclClass))
          res = EnclMethodEntry(javaName(enclClass), javaName(sym), javaType(sym))
        }
      }

      res
    }

    def getSuperInterfaces(csym: Symbol): Array[String] = {

        // Additional interface parents based on annotations and other cues
        def newParentForAttr(attr: Symbol): Option[Symbol] = attr match {
          case SerializableAttr => Some(SerializableClass)
          case CloneableAttr    => Some(CloneableClass)
          case RemoteAttr       => Some(RemoteInterfaceClass)
          case _                => None
        }

        /** Drop redundant interfaces (ones which are implemented by some other parent) from the immediate parents.
         *  This is important on Android because there is otherwise an interface explosion.
         */
        def minimizeInterfaces(lstIfaces: List[Symbol]): List[Symbol] = {
          var rest   = lstIfaces
          var leaves = List.empty[Symbol]
          while(!rest.isEmpty) {
            val candidate = rest.head
            val nonLeaf = leaves exists { lsym => lsym isSubClass candidate }
            if(!nonLeaf) {
              leaves = candidate :: (leaves filterNot { lsym => candidate isSubClass lsym })
            }
            rest = rest.tail
          }

          leaves
        }

      val ps = csym.info.parents
      val superInterfaces0: List[Symbol] = if(ps.isEmpty) Nil else csym.mixinClasses;
      val superInterfaces = superInterfaces0 ++ csym.annotations.flatMap(ann => newParentForAttr(ann.symbol)) distinct

      if(superInterfaces.isEmpty) EMPTY_STRING_ARRAY
      else mkArray(minimizeInterfaces(superInterfaces) map javaName)
    }

  } // end of trait BCClassGen

}
