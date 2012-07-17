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
            beanInfoCodeGen.genBeanInfoClass(cd.symbol, cunit, fieldSymbols(cd.symbol), methodSymbols(cd))
          }

        case ModuleDef(mods, name, impl) =>
          abort("Modules should have been eliminated by refchecks: " + tree)

        case ValDef(mods, name, tpt, rhs) =>
          () // fields are added in the case handler for ClassDef

        case dd : DefDef =>
          if(!skipMethodSymbol(dd.symbol)) { genDefDef(dd) }

        case Template(_, _, body) =>
          body foreach gen

        case _ =>
          abort("Illegal tree in gen: " + tree)
      }
    } // end of method gen(Tree)

    def genLoad(tree: Tree, expectedType: TypeKind) {
      // TODO
    }

    /* ---------------- helper utils invoked from gen() methods ---------------- */

    def genPlainClass(cd: ClassDef) {
      assert(cnode == null, "GenBCode detected nested methods.")
      innerClassBuffer.clear()

      val csym = cd.symbol
      thisName = javaName(csym)
      cnode = new asm.tree.ClassNode()
      initJClass(cnode, csym, thisName, getGenericSignature(csym, csym.owner), cunit)

      // TODO from visitSource to emitAnnotations

      // TODO addStaticInit, constructors

      addClassFields(csym)
      addSerialVUID(csym, cnode)

      gen(cd.impl)

      // TODO annotations, attributes

      addInnerClasses(csym, cnode)
      // TODO this is the time for dce, locals optimization, collapsing of jump-chains, etc.
      writeIfNotTooBig("" + csym.name, thisName, cnode, csym)
      cnode = null

    } // end of method genPlainClass()

    private def fieldSymbols(cls: Symbol): List[Symbol] = {
      for (f <- cls.info.decls.toList ; if !f.isMethod && f.isTerm && !f.isModule) yield f;
    }

    private def methodSymbols(cd: ClassDef): List[Symbol] = {
      cd.impl.body collect { case dd: DefDef if !skipMethodSymbol(dd.symbol) => dd.symbol }
    }

    private def skipMethodSymbol(msym: Symbol): Boolean = {
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

    private def genDefDef(dd: DefDef) {
      assert(mnode == null, "GenBCode detected flatten didn't run.")
      val msym = dd.symbol
      // clear method-specific stuff
          // TODO local-ranges table
          // TODO exh-handlers table
      val DefDef(mods, name, tparams, vparamss, tpt, rhs) = dd
      // add params
      assert(vparamss.isEmpty || vparamss.tail.isEmpty, "Malformed parameter list: " + vparamss)
      val paramIdx = if (msym.isStaticMember) 0 else 1;
      for (p <- vparamss.head) {
        // TODO val lv = new Local(p.symbol, toTypeKind(p.symbol.info), true)
      }

      val returnType =
        if (msym.isConstructor) UNIT
        else toTypeKind(msym.info.resultType)

      val isNative = msym.hasAnnotation(definitions.NativeAttr)
      val isAbstractMethod = msym.isDeferred || msym.owner.isInterface

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
            // TODO ctx1.bb.closeWith(RETURN(m.returnType), rhs.pos)
        }
      }
      mnode = null
    } // end of method genDefDef()

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

  } // end of class BCodePhase

} // end of class GenBCode
