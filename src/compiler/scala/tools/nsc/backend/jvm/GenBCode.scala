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
import asm.tree.ClassNode

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

    private var cunit: CompilationUnit     = null
    private val pkg = new mutable.Stack[String]
    private var cnode: asm.tree.ClassNode  = null
    private var thisName: String           = null // the internal name of the class being emitted
    private var mnode: asm.tree.MethodNode = null

    // bookkeeping for method-local vars and params
    private val locIdx = mutable.Map.empty[Symbol, Int] // (local-or-param-sym -> index-of-local-in-method)
    private var nxtIdx = 0 // next available index for local-var
    private def sizeOf(k: TypeKind): Int = if(k.isWideType) 2 else 1
    private def index(sym: Symbol): Int = {
      locIdx.getOrElseUpdate(sym, {
        val idx = nxtIdx;
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

    object bc extends JCodeMethodN {
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
      val csym        = msym.owner
      val Pair(flags, jmethod0) = initJMethod(
        cnode,
        msym,  isNative,
        csym,  csym.isInterface,
        params.map(p => javaType(p.symbol.info)),
        params.map(p => p.symbol.annotations)
      )
      mnode = jmethod0.asInstanceOf[asm.tree.MethodNode]

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
     *
     */
    private def genStat(tree: Tree) {
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

    def genLoad(tree: Tree, expectedType: TypeKind) {
      // TODO
    }

    /** Load the qualifier of `tree` on top of the stack. */
    def genLoadQualifier(tree: Tree) {
      // TODO
    }
  } // end of class BCodePhase

} // end of class GenBCode
