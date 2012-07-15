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
abstract class BCodeUtils extends SubComponent {
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

  } // end of trait BCInnerClassGen

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