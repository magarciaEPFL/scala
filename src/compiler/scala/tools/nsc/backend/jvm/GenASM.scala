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
 *  @author  Iulian Dragos (version 1.0, FJBG-based implementation)
 *  @author  Miguel Garcia (version 2.0,  ASM-based implementation)
 *
 * Documentation at http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/2012Q2/GenASM.pdf
 */
abstract class GenASM extends BCodeUtils {
  import global._
  import icodes._
  import icodes.opcodes._
  import definitions._

  val phaseName = "jvm"

  /** Create a new phase */
  override def newPhase(p: Phase): Phase = new AsmPhase(p)

  /** JVM code generation phase */
  class AsmPhase(prev: Phase) extends ICodePhase(prev) with BCCommonPhase {
    def name = phaseName
    override def erasedTypes = true
    def apply(cls: IClass) = sys.error("no implementation")

    override def run() {

      if (settings.debug.value)
        inform("[running phase " + name + " on icode]")

      // non-alive anon-closures already eliminated at the end of DeadCodeEliminationPhase.run()

      // For predictably ordered error messages.
      var sortedClasses   = classes.values.toList sortBy ("" + _.symbol.fullName)
      val bytecodeWriter  = initBytecodeWriter( sortedClasses filter { ic => isJavaEntryPoint(ic.symbol, ic.cunit) } map (_.symbol) )
      val plainCodeGen    = new JPlainBuilder(bytecodeWriter)
      val mirrorCodeGen   = new JMirrorBuilder(bytecodeWriter)
      val beanInfoCodeGen = new JBeanInfoBuilder(bytecodeWriter)

      while(!sortedClasses.isEmpty) {
        val c = sortedClasses.head

        if (isStaticModule(c.symbol) && isTopLevelModule(c.symbol)) {
          if (c.symbol.companionClass == NoSymbol) {
            mirrorCodeGen.genMirrorClass(c.symbol, c.cunit)
          } else {
            log("No mirror class for module with linked class: " + c.symbol.fullName)
          }
        }

        plainCodeGen.genClass(c)

        if (c.symbol hasAnnotation BeanInfoAttr) {
          beanInfoCodeGen.genBeanInfoClass(c.symbol, c.cunit, c.fields.map(_.symbol), c.methods.map(_.symbol))
        }

        sortedClasses = sortedClasses.tail
        classes -= c.symbol // GC opportunity
      }

      bytecodeWriter.close()
      classes.clear()
      reverseJavaName.clear()

      /* don't javaNameCache.clear() because that causes the following tests to fail:
       *   test/files/run/macro-repl-dontexpand.scala
       *   test/files/jvm/interpreter.scala
       * TODO but why? what use could javaNameCache possibly see once GenJVM is over?
       */

      /* TODO After emitting all class files (e.g., in a separate compiler phase) ASM can perform bytecode verification:
       *
       * (1) call the asm.util.CheckAdapter.verify() overload:
       *     public static void verify(ClassReader cr, ClassLoader loader, boolean dump, PrintWriter pw)
       *
       * (2) passing a custom ClassLoader to verify inter-dependent classes.
       *
       * Alternatively, an offline-bytecode verifier could be used (e.g. Maxine brings one as separate tool).
       */

    } // end of AsmPhase.run()

  } // end of class AsmPhase



  case class BlockInteval(start: BasicBlock, end: BasicBlock)

  /** builder of plain classes */
  class JPlainBuilder(bytecodeWriter: BytecodeWriter)
    extends JCommonBuilder(bytecodeWriter)
    with    BCClassGen
    with    JAndroidBuilder {

    def isParcelableClass = isAndroidParcelableClass(clasz.symbol)

    var clasz:    IClass = _           // this var must be assigned only by genClass()
    var jclass:   asm.ClassWriter = _  // the classfile being emitted
    var thisName: String = _           // the internal name of jclass

    def thisDescr: String = {
      assert(thisName != null, "thisDescr invoked too soon.")
      asm.Type.getObjectType(thisName).getDescriptor
    }

    def getCurrentCUnit(): CompilationUnit = { clasz.cunit }

    def genClass(c: IClass) {
      clasz = c
      innerClassBuffer.clear()

      thisName = javaName(c.symbol)
      jclass = new CClassWriter(extraProc)
      initJClass(jclass, c.symbol, thisName, getGenericSignature(c.symbol, c.symbol.owner))

      // typestate: entering mode with valid call sequences:
      //   [ visitSource ] [ visitOuterClass ] ( visitAnnotation | visitAttribute )*

      if(emitSource) {
        jclass.visitSource(c.cunit.source.toString,
                           null /* SourceDebugExtension */)
      }

      val enclM = getEnclosingMethodAttribute(clasz.symbol)
      if(enclM != null) {
        val EnclMethodEntry(className, methodName, methodType) = enclM
        jclass.visitOuterClass(className, methodName, methodType.getDescriptor)
      }

      // typestate: entering mode with valid call sequences:
      //   ( visitAnnotation | visitAttribute )*

      val ssa = getAnnotPickle(thisName, c.symbol)
      jclass.visitAttribute(if(ssa.isDefined) pickleMarkerLocal else pickleMarkerForeign)
      emitAnnotations(jclass, c.symbol.annotations ++ ssa)

      // typestate: entering mode with valid call sequences:
      //   ( visitInnerClass | visitField | visitMethod )* visitEnd

      if (isStaticModule(c.symbol) || isParcelableClass) {

        if (isStaticModule(c.symbol)) { addModuleInstanceField() }
        addStaticInit(c.lookupStaticCtor)

      } else {

        for (constructor <- c.lookupStaticCtor) {
          addStaticInit(Some(constructor))
        }
        val skipStaticForwarders = (c.symbol.isInterface || settings.noForwarders.value)
        if (!skipStaticForwarders) {
          val lmoc = c.symbol.companionModule
          // add static forwarders if there are no name conflicts; see bugs #363 and #1735
          if (lmoc != NoSymbol) {
            // it must be a top level class (name contains no $s)
            val isCandidateForForwarders = {
              afterPickler { !(lmoc.name.toString contains '$') && lmoc.hasModuleFlag && !lmoc.isImplClass && !lmoc.isNestedClass }
            }
            if (isCandidateForForwarders) {
              log("Adding static forwarders from '%s' to implementations in '%s'".format(c.symbol, lmoc))
              addForwarders(isRemote(clasz.symbol), jclass, thisName, lmoc.moduleClass)
            }
          }
        }

      }

      addSerialVUID(clasz.symbol, jclass)

      clasz.fields  foreach genField
      clasz.methods foreach { im => genMethod(im, c.symbol.isInterface) }

      addInnerClasses(clasz.symbol, jclass)
      jclass.visitEnd()
      writeIfNotTooBig("" + c.symbol.name, thisName, jclass, c.symbol)

    }

    def genField(f: IField) {
      debuglog("Adding field: " + f.symbol.fullName)

      val javagensig = getGenericSignature(f.symbol, clasz.symbol)

      val flags = mkFlags(
        javaFieldFlags(f.symbol),
        if(isDeprecated(f.symbol)) asm.Opcodes.ACC_DEPRECATED else 0 // ASM pseudo access flag
      )

      val jfield: asm.FieldVisitor = jclass.visitField(
        flags,
        javaName(f.symbol),
        javaType(f.symbol.tpe).getDescriptor(),
        javagensig,
        null // no initial value
      )

      emitAnnotations(jfield, f.symbol.annotations)
      jfield.visitEnd()
    }

    var method:  IMethod = _
    var jmethod: asm.MethodVisitor = _
    var jMethodName: String = _

    @inline final def emit(opc: Int) { jmethod.visitInsn(opc) }

    def genMethod(m: IMethod, isJInterface: Boolean) {

        def isClosureApply(sym: Symbol): Boolean = {
          (sym.name == nme.apply) &&
          sym.owner.isSynthetic &&
          sym.owner.tpe.parents.exists { t =>
            val TypeRef(_, sym, _) = t
            FunctionClass contains sym
          }
        }

      if (m.symbol.isStaticConstructor || definitions.isGetClass(m.symbol)) return

      debuglog("Generating method " + m.symbol.fullName)
      method = m
      computeLocalVarsIndex(m)

      var resTpe: asm.Type = javaType(m.symbol.tpe.resultType)
      if (m.symbol.isClassConstructor)
        resTpe = asm.Type.VOID_TYPE

      val flags = mkFlags(
        javaFlags(m.symbol),
        if (isJInterface)          asm.Opcodes.ACC_ABSTRACT   else 0,
        if (m.symbol.isStrictFP)   asm.Opcodes.ACC_STRICT     else 0,
        if (method.native)         asm.Opcodes.ACC_NATIVE     else 0, // native methods of objects are generated in mirror classes
        if(isDeprecated(m.symbol)) asm.Opcodes.ACC_DEPRECATED else 0  // ASM pseudo access flag
      )

      // TODO needed? for(ann <- m.symbol.annotations) { ann.symbol.initialize }
      val jgensig = getGenericSignature(m.symbol, clasz.symbol)
      addRemoteExceptionAnnot(isRemote(clasz.symbol), hasPublicBitSet(flags), m.symbol)
      val (excs, others) = m.symbol.annotations partition (_.symbol == ThrowsClass)
      val thrownExceptions: List[String] = getExceptions(excs)

      jMethodName = javaName(m.symbol)
      val mdesc = asm.Type.getMethodDescriptor(resTpe, (m.params map (p => javaType(p.kind))): _*)
      jmethod = jclass.visitMethod(
        flags,
        jMethodName,
        mdesc,
        jgensig,
        mkArray(thrownExceptions)
      )

      // TODO param names: (m.params map (p => javaName(p.sym)))

      // typestate: entering mode with valid call sequences:
      //   [ visitAnnotationDefault ] ( visitAnnotation | visitParameterAnnotation | visitAttribute )*

      emitAnnotations(jmethod, others)
      emitParamAnnotations(jmethod, m.params.map(_.sym.annotations))

      // typestate: entering mode with valid call sequences:
      //   [ visitCode ( visitFrame | visitXInsn | visitLabel | visitTryCatchBlock | visitLocalVariable | visitLineNumber )* visitMaxs ] visitEnd
      // In addition, the visitXInsn and visitLabel methods must be called in the sequential order of the bytecode instructions of the visited code,
      // visitTryCatchBlock must be called before the labels passed as arguments have been visited, and
      // the visitLocalVariable and visitLineNumber methods must be called after the labels passed as arguments have been visited.

      val hasAbstractBitSet = ((flags & asm.Opcodes.ACC_ABSTRACT) != 0)
      val hasCodeAttribute  = (!hasAbstractBitSet && !method.native)
      if (hasCodeAttribute) {

        jmethod.visitCode()

        if (emitVars && isClosureApply(method.symbol)) {
          // add a fake local for debugging purposes
          val outerField = clasz.symbol.info.decl(nme.OUTER_LOCAL)
          if (outerField != NoSymbol) {
            log("Adding fake local to represent outer 'this' for closure " + clasz)
            val _this =
              new Local(method.symbol.newVariable(nme.FAKE_LOCAL_THIS),
                        toTypeKind(outerField.tpe),
                        false)
            m.locals = m.locals ::: List(_this)
            computeLocalVarsIndex(m) // since we added a new local, we need to recompute indexes
            jmethod.visitVarInsn(asm.Opcodes.ALOAD, 0)
            jmethod.visitFieldInsn(asm.Opcodes.GETFIELD,
                                   javaName(clasz.symbol), // field owner
                                   javaName(outerField),   // field name
                                   descriptor(outerField)  // field descriptor
            )
            assert(_this.kind.isReferenceType, _this.kind)
            jmethod.visitVarInsn(asm.Opcodes.ASTORE, indexOf(_this))
          }
        }

        assert( m.locals forall { local => (m.params contains local) == local.arg }, m.locals )

        val hasStaticBitSet = ((flags & asm.Opcodes.ACC_STATIC) != 0)
        genCode(m, emitVars, hasStaticBitSet)

        jmethod.visitMaxs(0, 0) // just to follow protocol, dummy arguments
      }

      jmethod.visitEnd()

    }

    def addModuleInstanceField() {
      val fv =
        jclass.visitField(PublicStaticFinal, // TODO confirm whether we really don't want ACC_SYNTHETIC nor ACC_DEPRECATED
                          strMODULE_INSTANCE_FIELD,
                          thisDescr,
                          null, // no java-generic-signature
                          null  // no initial value
        )

      // typestate: entering mode with valid call sequences:
      //   ( visitAnnotation | visitAttribute )* visitEnd.

      fv.visitEnd()
    }


    /* Typestate: should be called before being done with emitting fields (because it invokes addCreatorCode() which adds an IField to the current IClass). */
    def addStaticInit(mopt: Option[IMethod]) {

      val clinitMethod: asm.MethodVisitor = jclass.visitMethod(
        PublicStatic, // TODO confirm whether we really don't want ACC_SYNTHETIC nor ACC_DEPRECATED
        CLASS_CONSTRUCTOR_NAME,
        mdesc_arglessvoid,
        null, // no java-generic-signature
        null  // no throwable exceptions
      )

      mopt match {

       	case Some(m) =>

          val oldLastBlock = m.lastBlock
          val lastBlock = m.newBlock()
          oldLastBlock.replaceInstruction(oldLastBlock.length - 1, JUMP(lastBlock))

          if (isStaticModule(clasz.symbol)) {
            // call object's private ctor from static ctor
            lastBlock emit NEW(REFERENCE(m.symbol.enclClass))
            lastBlock emit CALL_METHOD(m.symbol.enclClass.primaryConstructor, Static(true))
          }

          if (isParcelableClass) { addAndroidCreatorCode(lastBlock) }

          lastBlock emit RETURN(UNIT)
          lastBlock.close

       	  method = m
       	  jmethod = clinitMethod
          jMethodName = CLASS_CONSTRUCTOR_NAME
          jmethod.visitCode()
       	  genCode(m, false, true)
          jmethod.visitMaxs(0, 0) // just to follow protocol, dummy arguments
          jmethod.visitEnd()

       	case None =>
          clinitMethod.visitCode()
          legacyStaticInitializer(clinitMethod)
          clinitMethod.visitMaxs(0, 0) // just to follow protocol, dummy arguments
          clinitMethod.visitEnd()

      }
    }

    /* Typestate: should be called before emitting fields (because it adds an IField to the current IClass). */
    private def addAndroidCreatorCode(block: BasicBlock) {
      val fieldSymbol = (
        clasz.symbol.newValue(newTermName(androidFieldName), NoPosition, Flags.STATIC | Flags.FINAL)
          setInfo AndroidCreatorClass.tpe
      )
      val methodSymbol = definitions.getMember(clasz.symbol.companionModule, androidFieldName)
      clasz addField new IField(fieldSymbol)
      block emit CALL_METHOD(methodSymbol, Static(false))
      block emit STORE_FIELD(fieldSymbol, true)
    }

    /* used only from addStaticInit() */
    private def legacyStaticInitializer(clinit: asm.MethodVisitor) {
      if (isStaticModule(clasz.symbol)) {
        clinit.visitTypeInsn(asm.Opcodes.NEW, thisName)
        clinit.visitMethodInsn(asm.Opcodes.INVOKESPECIAL,
                               thisName, INSTANCE_CONSTRUCTOR_NAME, mdesc_arglessvoid)
      }

      if (isParcelableClass) { legacyAddCreatorCode(clinit, jclass, clasz.symbol, thisName) }

      clinit.visitInsn(asm.Opcodes.RETURN)
    }

    // -----------------------------------------------------------------------------------------
    // Emitting bytecode instructions.
    // -----------------------------------------------------------------------------------------

    object jcode extends JCodeMethodV {
      override def jmethod = JPlainBuilder.this.jmethod
    }

    /** Invoked from genMethod() and addStaticInit() */
    def genCode(m: IMethod,
                emitVars: Boolean, // this param name hides the instance-level var
                isStatic: Boolean) {


      newNormal.normalize(m)

      // ------------------------------------------------------------------------------------------------------------
      // Part 1 of genCode(): setting up one-to-one correspondence between ASM Labels and BasicBlocks `linearization`
      // ------------------------------------------------------------------------------------------------------------

      val linearization: List[BasicBlock] = linearizer.linearize(m)
      if(linearization.isEmpty) { return }

      var isModuleInitialized = false

      val labels: collection.Map[BasicBlock, asm.Label] = mutable.HashMap(linearization map (_ -> new asm.Label()) : _*)

      val onePastLast = new asm.Label // token for the mythical instruction past the last instruction in the method being emitted

      // maps a BasicBlock b to the Label that corresponds to b's successor in the linearization. The last BasicBlock is mapped to the onePastLast label.
      val linNext: collection.Map[BasicBlock, asm.Label] = {
        val result = mutable.HashMap.empty[BasicBlock, asm.Label]
        var rest = linearization
        var prev = rest.head
        rest = rest.tail
        while(!rest.isEmpty) {
          result += (prev -> labels(rest.head))
          prev = rest.head
          rest = rest.tail
        }
        assert(!result.contains(prev))
        result += (prev -> onePastLast)

        result
      }

      // ------------------------------------------------------------------------------------------------------------
      // Part 2 of genCode(): demarcating exception handler boundaries (visitTryCatchBlock() must be invoked before visitLabel() in genBlock())
      // ------------------------------------------------------------------------------------------------------------

        /**Generate exception handlers for the current method.
         *
         * Quoting from the JVMS 4.7.3 The Code Attribute
         * The items of the Code_attribute structure are as follows:
         *   . . .
         *   exception_table[]
         *     Each entry in the exception_table array describes one
         *     exception handler in the code array. The order of the handlers in
         *     the exception_table array is significant.
         *     Each exception_table entry contains the following four items:
         *       start_pc, end_pc:
         *         ... The value of end_pc either must be a valid index into
         *         the code array of the opcode of an instruction or must be equal to code_length,
         *         the length of the code array.
         *       handler_pc:
         *         The value of the handler_pc item indicates the start of the exception handler
         *       catch_type:
         *         ... If the value of the catch_type item is zero,
         *         this exception handler is called for all exceptions.
         *         This is used to implement finally
         */
        def genExceptionHandlers() {

          /** Return a list of pairs of intervals where the handler is active.
           *  Each interval is closed on both ends, ie. inclusive both in the left and right endpoints: [start, end].
           *  Preconditions:
           *    - e.covered non-empty
           *  Postconditions for the result:
           *    - always non-empty
           *    - intervals are sorted as per `linearization`
           *    - the argument's `covered` blocks have been grouped into maximally contiguous intervals,
           *      ie. between any two intervals in the result there is a non-empty gap.
           *    - each of the `covered` blocks in the argument is contained in some interval in the result
           */
          def intervals(e: ExceptionHandler): List[BlockInteval] = {
            assert(e.covered.nonEmpty, e)
            var result: List[BlockInteval] = Nil
            var rest = linearization

            // find intervals
            while(!rest.isEmpty) {
              // find interval start
              var start: BasicBlock = null
              while(!rest.isEmpty && (start eq null)) {
                if(e.covered(rest.head)) { start = rest.head }
                rest = rest.tail
              }
              if(start ne null) {
                // find interval end
                var end = start // for the time being
                while(!rest.isEmpty && (e.covered(rest.head))) {
                  end  = rest.head
                  rest = rest.tail
                }
                result = BlockInteval(start, end) :: result
              }
            }

            assert(result.nonEmpty, e)

            result
          }

          /* TODO test/files/run/exceptions-2.scala displays an ExceptionHandler.covered that contains
           * blocks not in the linearization (dead-code?). Is that well-formed or not?
           * For now, we ignore those blocks (after all, that's what `genBlocks(linearization)` in effect does).
           */
          for (e <- this.method.exh) {
            val ignore: Set[BasicBlock] = (e.covered filterNot { b => linearization contains b } )
            // TODO someday assert(ignore.isEmpty, "an ExceptionHandler.covered contains blocks not in the linearization (dead-code?)")
            if(ignore.nonEmpty) {
              e.covered  = e.covered filterNot ignore
            }
          }

          // an ExceptionHandler lacking covered blocks doesn't get an entry in the Exceptions table.
          // TODO in that case, ExceptionHandler.cls doesn't go through javaName(). What if cls is an inner class?
          for (e <- this.method.exh ; if e.covered.nonEmpty ; p <- intervals(e)) {
            debuglog("Adding exception handler " + e + "at block: " + e.startBlock + " for " + method +
                     " from: " + p.start + " to: " + p.end + " catching: " + e.cls);
            val cls: String = if (e.cls == NoSymbol || e.cls == ThrowableClass) null
                              else javaName(e.cls)
            jmethod.visitTryCatchBlock(labels(p.start), linNext(p.end), labels(e.startBlock), cls)
          }
        } // end of genCode()'s genExceptionHandlers()

      if (m.exh.nonEmpty) { genExceptionHandlers() }

      // ------------------------------------------------------------------------------------------------------------
      // Part 3 of genCode(): "Infrastructure" to later emit debug info for local variables and method params (LocalVariablesTable bytecode attribute).
      // ------------------------------------------------------------------------------------------------------------

        case class LocVarEntry(local: Local, start: asm.Label, end: asm.Label) // start is inclusive while end exclusive.

        case class Interval(lstart: asm.Label, lend: asm.Label) {
          @inline final def start = lstart.getOffset
          @inline final def end   = lend.getOffset

          def precedes(that: Interval): Boolean = { this.end < that.start }

          def overlaps(that: Interval): Boolean = { !(this.precedes(that) || that.precedes(this)) }

          def mergeWith(that: Interval): Interval = {
            val newStart = if(this.start <= that.start) this.lstart else that.lstart;
            val newEnd   = if(this.end   <= that.end)   that.lend   else this.lend;
            Interval(newStart, newEnd)
          }

          def repOK: Boolean = { start <= end }

        }

        /** Track those instruction ranges where certain locals are in scope. Used to later emit the LocalVariableTable attribute (JVMS 4.7.13) */
        object scoping {

          private val pending = mutable.Map.empty[Local, mutable.Stack[Label]]
          private var seen: List[LocVarEntry] = Nil

          private def fuse(ranges: List[Interval], added: Interval): List[Interval] = {
            assert(added.repOK, added)
            if(ranges.isEmpty) { return List(added) }
            // precond: ranges is sorted by increasing start
            var fused: List[Interval] = Nil
            var done = false
            var rest = ranges
            while(!done && rest.nonEmpty) {
              val current = rest.head
              assert(current.repOK, current)
              rest = rest.tail
              if(added precedes current) {
                fused = fused ::: ( added :: current :: rest )
                done = true
              } else if(current overlaps added) {
                fused = fused ::: ( added.mergeWith(current) :: rest )
                done = true
              }
            }
            if(!done) { fused = fused ::: List(added) }
            assert(repOK(fused), fused)

            fused
          }

          def pushScope(lv: Local, start: Label) {
            val st = pending.getOrElseUpdate(lv, mutable.Stack.empty[Label])
            st.push(start)
          }
          def popScope(lv: Local, end: Label, iPos: Position) {
            pending.get(lv) match {
              case Some(st) if st.nonEmpty =>
                val start = st.pop()
                seen ::= LocVarEntry(lv, start, end)
              case _ =>
                // TODO SI-6049
                getCurrentCUnit().warning(iPos, "Visited SCOPE_EXIT before visiting corresponding SCOPE_ENTER. SI-6049")
            }
          }

          def getMerged(): collection.Map[Local, List[Interval]] = {
            // TODO should but isn't: unbalanced start(s) of scope(s)
            val shouldBeEmpty = pending filter { p => val Pair(k, st) = p; st.nonEmpty };

            val merged = mutable.Map.empty[Local, List[Interval]]

              def addToMerged(lv: Local, start: Label, end: Label) {
                val ranges = merged.getOrElseUpdate(lv, Nil)
                val coalesced = fuse(ranges, Interval(start, end))
                merged.update(lv, coalesced)
              }

            for(LocVarEntry(lv, start, end) <- seen) { addToMerged(lv, start, end) }

            /* for each var with unbalanced start(s) of scope(s):
                 (a) take the earliest start (among unbalanced and balanced starts)
                 (b) take the latest end (onePastLast if none available)
                 (c) merge the thus made-up interval
             */
            for(Pair(k, st) <- shouldBeEmpty) {
              var start = st.toList.sortBy(_.getOffset).head
              if(merged.isDefinedAt(k)) {
                val balancedStart = merged(k).head.lstart
                if(balancedStart.getOffset < start.getOffset) {
                  start = balancedStart;
                }
              }
              val endOpt: Option[Label] = for(ranges <- merged.get(k)) yield ranges.last.lend;
              val end = endOpt.getOrElse(onePastLast)
              addToMerged(k, start, end)
            }

            merged
          }

          private def repOK(fused: List[Interval]): Boolean = {
            fused match {
              case Nil      => true
              case h :: Nil => h.repOK
              case h :: n :: rest =>
                h.repOK && h.precedes(n) && !h.overlaps(n) && repOK(n :: rest)
            }
          }

        }

      def genLocalVariableTable() {
        // adding `this` and method params.
        if (!isStatic) {
          jmethod.visitLocalVariable("this", thisDescr, null, labels(m.startBlock), onePastLast, 0)
        }
        for(lv <- m.params) {
          jmethod.visitLocalVariable(javaName(lv.sym), descriptor(lv.kind), null, labels(m.startBlock), onePastLast, indexOf(lv))
        }
        // adding non-param locals
        var anonCounter = 0
        var fltnd: List[Triple[String, Local, Interval]] = Nil
        for(Pair(local, ranges) <- scoping.getMerged()) {
          var name = javaName(local.sym)
          if (name == null) {
            anonCounter += 1;
            name = "<anon" + anonCounter + ">"
          }
          for(intrvl <- ranges) {
            fltnd ::= Triple(name, local, intrvl)
          }
        }
        // quest for deterministic output that Map.toList doesn't provide (so that ant test.stability doesn't complain).
        val srtd = fltnd.sortBy { kr =>
          val Triple(name: String, local: Local, intrvl: Interval) = kr

          Triple(intrvl.start, intrvl.end - intrvl.start, name)  // ie sort by (start, length, name)
        }

        for(Triple(name, local, Interval(start, end)) <- srtd) {
          jmethod.visitLocalVariable(name, descriptor(local.kind), null, start, end, indexOf(local))
        }
        // "There may be no more than one LocalVariableTable attribute per local variable in the Code attribute"
      }

      // ------------------------------------------------------------------------------------------------------------
      // Part 4 of genCode(): Bookkeeping (to later emit debug info) of association between line-number and instruction position.
      // ------------------------------------------------------------------------------------------------------------

      case class LineNumberEntry(line: Int, start: asm.Label)
      var lastLineNr: Int = -1
      var lnEntries: List[LineNumberEntry] = Nil

      // ------------------------------------------------------------------------------------------------------------
      // Part 5 of genCode(): "Utilities" to emit code proper (most prominently: genBlock()).
      // ------------------------------------------------------------------------------------------------------------

      var nextBlock: BasicBlock = linearization.head

      def genBlocks(l: List[BasicBlock]): Unit = l match {
        case Nil => ()
        case x :: Nil => nextBlock = null; genBlock(x)
        case x :: y :: ys => nextBlock = y; genBlock(x); genBlocks(y :: ys)
      }

      def isAccessibleFrom(target: Symbol, site: Symbol): Boolean = {
        target.isPublic || target.isProtected && {
          (site.enclClass isSubClass target.enclClass) ||
          (site.enclosingPackage == target.privateWithin)
        }
      } // end of genCode()'s isAccessibleFrom()

      def genCallMethod(call: CALL_METHOD) {
        val CALL_METHOD(method, style) = call
        val siteSymbol  = clasz.symbol
        val hostSymbol  = call.hostClass
        val methodOwner = method.owner
        // info calls so that types are up to date; erasure may add lateINTERFACE to traits
        hostSymbol.info ; methodOwner.info

        def isInterfaceCall(sym: Symbol) = (
             sym.isInterface && methodOwner != ObjectClass
          || sym.isJavaDefined && sym.isNonBottomSubClass(ClassfileAnnotationClass)
        )
        // whether to reference the type of the receiver or
        // the type of the method owner (if not an interface!)
        val useMethodOwner = (
             style != Dynamic
          || !isInterfaceCall(hostSymbol) && isAccessibleFrom(methodOwner, siteSymbol)
          || hostSymbol.isBottomClass
        )
        val receiver = if (useMethodOwner) methodOwner else hostSymbol
        val jowner   = javaName(receiver)
        val jname    = javaName(method)
        val jtype    = javaType(method).getDescriptor()

        def dbg(invoke: String) {
          debuglog("%s %s %s.%s:%s".format(invoke, receiver.accessString, jowner, jname, jtype))
        }

        def initModule() {
          // we initialize the MODULE$ field immediately after the super ctor
          if (isStaticModule(siteSymbol) && !isModuleInitialized &&
              jMethodName == INSTANCE_CONSTRUCTOR_NAME &&
              jname == INSTANCE_CONSTRUCTOR_NAME) {
            isModuleInitialized = true
            jmethod.visitVarInsn(asm.Opcodes.ALOAD, 0)
            jmethod.visitFieldInsn(asm.Opcodes.PUTSTATIC, thisName, strMODULE_INSTANCE_FIELD, thisDescr)
          }
        }

        style match {
          case Static(true)                         => dbg("invokespecial");  jcode.invokespecial  (jowner, jname, jtype)
          case Static(false)                        => dbg("invokestatic");   jcode.invokestatic   (jowner, jname, jtype)
          case Dynamic if isInterfaceCall(receiver) => dbg("invokinterface"); jcode.invokeinterface(jowner, jname, jtype)
          case Dynamic                              => dbg("invokevirtual");  jcode.invokevirtual  (jowner, jname, jtype)
          case SuperCall(_)                         =>
            dbg("invokespecial")
            jcode.invokespecial(jowner, jname, jtype)
            initModule()
        }
      } // end of genCode()'s genCallMethod()

      def genBlock(b: BasicBlock) {
        jmethod.visitLabel(labels(b))

        import asm.Opcodes;

        debuglog("Generating code for block: " + b)

        // val lastInstr = b.lastInstruction

        for (instr <- b) {

          if(instr.pos.isDefined) {
            val iPos = instr.pos
            val currentLineNr = iPos.line
            val skip = (currentLineNr == lastLineNr) // if(iPos.isRange) iPos.sameRange(lastPos) else
            if(!skip) {
              lastLineNr = currentLineNr
              val lineLab = new asm.Label
              jmethod.visitLabel(lineLab)
              lnEntries ::= LineNumberEntry(currentLineNr, lineLab)
            }
          }

          (instr.category: @scala.annotation.switch) match {

            case icodes.localsCat => (instr: @unchecked) match {
                case THIS(_)            => jmethod.visitVarInsn(Opcodes.ALOAD, 0)
                case LOAD_LOCAL(local)  => jcode.load(indexOf(local), local.kind)
                case STORE_LOCAL(local) => jcode.store(indexOf(local), local.kind)
                case STORE_THIS(_)      =>
                  // this only works for impl classes because the self parameter comes first
                  // in the method signature. If that changes, this code has to be revisited.
                  jmethod.visitVarInsn(Opcodes.ASTORE, 0)

                case SCOPE_ENTER(lv) =>
                  // locals removed by closelim (via CopyPropagation) may have left behind SCOPE_ENTER, SCOPE_EXIT that are to be ignored
                  val relevant = (!lv.sym.isSynthetic && m.locals.contains(lv))
                  if(relevant) { // TODO check: does GenICode emit SCOPE_ENTER, SCOPE_EXIT for synthetic vars?
                    // this label will have DEBUG bit set in its flags (ie ASM ignores it for dataflow purposes)
                    // similarly, these labels aren't tracked in the `labels` map.
                    val start = new asm.Label
                    jmethod.visitLabel(start)
                    scoping.pushScope(lv, start)
                  }

                case SCOPE_EXIT(lv) =>
                  val relevant = (!lv.sym.isSynthetic && m.locals.contains(lv))
                  if(relevant) {
                    // this label will have DEBUG bit set in its flags (ie ASM ignores it for dataflow purposes)
                    // similarly, these labels aren't tracked in the `labels` map.
                    val end = new asm.Label
                    jmethod.visitLabel(end)
                    scoping.popScope(lv, end, instr.pos)
                  }
            }

            case icodes.stackCat => (instr: @unchecked) match {

              case LOAD_MODULE(module) =>
                // assert(module.isModule, "Expected module: " + module)
                debuglog("generating LOAD_MODULE for: " + module + " flags: " + Flags.flagsToString(module.flags));
                if (clasz.symbol == module.moduleClass && jMethodName != nme.readResolve.toString) {
                  jmethod.visitVarInsn(Opcodes.ALOAD, 0)
                } else {
                  jmethod.visitFieldInsn(
                    Opcodes.GETSTATIC,
                    javaName(module) /* + "$" */ ,
                    strMODULE_INSTANCE_FIELD,
                    descriptor(module)
                  )
                }

              case DROP(kind)   => emit(if(kind.isWideType) Opcodes.POP2 else Opcodes.POP)

              case DUP(kind)    => emit(if(kind.isWideType) Opcodes.DUP2 else Opcodes.DUP)

              case LOAD_EXCEPTION(_) => ()
            }

            case icodes.constCat => jcode.genConstant(instr.asInstanceOf[CONSTANT].constant)

            case icodes.arilogCat => genPrimitive(instr.asInstanceOf[CALL_PRIMITIVE].primitive, instr.pos)

            case icodes.castsCat => (instr: @unchecked) match {

              case IS_INSTANCE(tpe) =>
                val jtyp: asm.Type =
                  tpe match {
                    case REFERENCE(cls) => asm.Type.getObjectType(javaName(cls))
                    case ARRAY(elem)    => javaArrayType(javaType(elem))
                    case _              => abort("Unknown reference type in IS_INSTANCE: " + tpe)
                  }
                jmethod.visitTypeInsn(Opcodes.INSTANCEOF, jtyp.getInternalName)

              case CHECK_CAST(tpe) =>
                tpe match {

                  case REFERENCE(cls) =>
                    if (cls != ObjectClass) { // No need to checkcast for Objects
                      jmethod.visitTypeInsn(Opcodes.CHECKCAST, javaName(cls))
                    }

                  case ARRAY(elem)    =>
                    val iname = javaArrayType(javaType(elem)).getInternalName
                    jmethod.visitTypeInsn(Opcodes.CHECKCAST, iname)

                  case _              => abort("Unknown reference type in IS_INSTANCE: " + tpe)
                }

            }

            case icodes.objsCat  => (instr: @unchecked) match {

              case BOX(kind) =>
                val MethodNameAndType(mname, mdesc) = jBoxTo(kind)
                jcode.invokestatic(BoxesRunTime, mname, mdesc)

              case UNBOX(kind) =>
                val MethodNameAndType(mname, mdesc) = jUnboxTo(kind)
                jcode.invokestatic(BoxesRunTime, mname, mdesc)

              case NEW(REFERENCE(cls)) =>
                val className = javaName(cls)
                jmethod.visitTypeInsn(Opcodes.NEW, className)

              case MONITOR_ENTER() => emit(Opcodes.MONITORENTER)
              case MONITOR_EXIT()  => emit(Opcodes.MONITOREXIT)
            }

            case icodes.fldsCat  => (instr: @unchecked) match {

              case lf @ LOAD_FIELD(field, isStatic) =>
                var owner = javaName(lf.hostClass)
                debuglog("LOAD_FIELD with owner: " + owner + " flags: " + Flags.flagsToString(field.owner.flags))
                val fieldJName = javaName(field)
                val fieldDescr = descriptor(field)
                val opc = if (isStatic) Opcodes.GETSTATIC else Opcodes.GETFIELD
                jmethod.visitFieldInsn(opc, owner, fieldJName, fieldDescr)

              case STORE_FIELD(field, isStatic) =>
                val owner = javaName(field.owner)
                val fieldJName = javaName(field)
                val fieldDescr = descriptor(field)
                val opc = if (isStatic) Opcodes.PUTSTATIC else Opcodes.PUTFIELD
                jmethod.visitFieldInsn(opc, owner, fieldJName, fieldDescr)

            }

            case icodes.mthdsCat => (instr: @unchecked) match {

              /** Special handling to access native Array.clone() */
              case call @ CALL_METHOD(definitions.Array_clone, Dynamic) =>
                val target: String = javaType(call.targetTypeKind).getInternalName
                jcode.invokevirtual(target, "clone", mdesc_arrayClone)

              case call @ CALL_METHOD(method, style) => genCallMethod(call)

            }

            case icodes.arraysCat => (instr: @unchecked) match {
              case LOAD_ARRAY_ITEM(kind)    => jcode.aload(kind)
              case STORE_ARRAY_ITEM(kind)   => jcode.astore(kind)
              case CREATE_ARRAY(elem, 1)    => jcode newarray elem
              case CREATE_ARRAY(elem, dims) => jmethod.visitMultiANewArrayInsn(descriptor(ArrayN(elem, dims)), dims)
            }

            case icodes.jumpsCat => (instr: @unchecked) match {

              case sw @ SWITCH(tagss, branches) =>
                assert(branches.length == tagss.length + 1, sw)
                val flatSize     = sw.flatTagsCount
                val flatKeys     = new Array[Int](flatSize)
                val flatBranches = new Array[asm.Label](flatSize)

                var restTagss    = tagss
                var restBranches = branches
                var k = 0 // ranges over flatKeys and flatBranches
                while(restTagss.nonEmpty) {
                  val currLabel = labels(restBranches.head)
                  for(cTag <- restTagss.head) {
                    flatKeys(k)     = cTag;
                    flatBranches(k) = currLabel
                    k += 1
                  }
                  restTagss    = restTagss.tail
                  restBranches = restBranches.tail
                }
                val defaultLabel = labels(restBranches.head)
                assert(restBranches.tail.isEmpty)
                debuglog("Emitting SWITCH:\ntags: " + tagss + "\nbranches: " + branches)
                jcode.emitSWITCH(flatKeys, flatBranches, defaultLabel, MIN_SWITCH_DENSITY)

              case JUMP(whereto) =>
                if (nextBlock != whereto) {
                  jcode goTo labels(whereto)
                }

              case CJUMP(success, failure, cond, kind) =>
                if(kind.isIntSizedType) { // BOOL, BYTE, CHAR, SHORT, or INT
                  if (nextBlock == success) {
                    jcode.emitIF_ICMP(cond.negate, labels(failure))
                    // .. and fall through to success label
                  } else {
                    jcode.emitIF_ICMP(cond, labels(success))
                    if (nextBlock != failure) { jcode goTo labels(failure) }
                  }
                } else if(kind.isRefOrArrayType) { // REFERENCE(_) | ARRAY(_)
                  if (nextBlock == success) {
                    jcode.emitIF_ACMP(cond.negate, labels(failure))
                    // .. and fall through to success label
                  } else {
                    jcode.emitIF_ACMP(cond, labels(success))
                    if (nextBlock != failure) { jcode goTo labels(failure) }
                  }
                } else {
                  (kind: @unchecked) match {
                    case LONG   => emit(Opcodes.LCMP)
                    case FLOAT  =>
                      if (cond == LT || cond == LE) emit(Opcodes.FCMPG)
                      else emit(Opcodes.FCMPL)
                    case DOUBLE =>
                      if (cond == LT || cond == LE) emit(Opcodes.DCMPG)
                      else emit(Opcodes.DCMPL)
                  }
                  if (nextBlock == success) {
                    jcode.emitIF(cond.negate, labels(failure))
                    // .. and fall through to success label
                  } else {
                    jcode.emitIF(cond, labels(success))
                    if (nextBlock != failure) { jcode goTo labels(failure) }
                  }
                }

              case CZJUMP(success, failure, cond, kind) =>
                if(kind.isIntSizedType) { // BOOL, BYTE, CHAR, SHORT, or INT
                  if (nextBlock == success) {
                    jcode.emitIF(cond.negate, labels(failure))
                  } else {
                    jcode.emitIF(cond, labels(success))
                    if (nextBlock != failure) { jcode goTo labels(failure) }
                  }
                } else if(kind.isRefOrArrayType) { // REFERENCE(_) | ARRAY(_)
                  val Success = success
                  val Failure = failure
                  // @unchecked because references aren't compared with GT, GE, LT, LE.
                  ((cond, nextBlock) : @unchecked) match {
                    case (EQ, Success) => jcode emitIFNONNULL labels(failure)
                    case (NE, Failure) => jcode emitIFNONNULL labels(success)
                    case (EQ, Failure) => jcode emitIFNULL    labels(success)
                    case (NE, Success) => jcode emitIFNULL    labels(failure)
                    case (EQ, _) =>
                      jcode emitIFNULL labels(success)
                      jcode goTo labels(failure)
                    case (NE, _) =>
                      jcode emitIFNONNULL labels(success)
                      jcode goTo labels(failure)
                  }
                } else {
                  (kind: @unchecked) match {
                    case LONG   =>
                      emit(Opcodes.LCONST_0)
                      emit(Opcodes.LCMP)
                    case FLOAT  =>
                      emit(Opcodes.FCONST_0)
                      if (cond == LT || cond == LE) emit(Opcodes.FCMPG)
                      else emit(Opcodes.FCMPL)
                    case DOUBLE =>
                      emit(Opcodes.DCONST_0)
                      if (cond == LT || cond == LE) emit(Opcodes.DCMPG)
                      else emit(Opcodes.DCMPL)
                  }
                  if (nextBlock == success) {
                    jcode.emitIF(cond.negate, labels(failure))
                  } else {
                    jcode.emitIF(cond, labels(success))
                    if (nextBlock != failure) { jcode goTo labels(failure) }
                  }
                }

            }

            case icodes.retCat   => (instr: @unchecked) match {
              case RETURN(kind) => jcode emitRETURN kind
              case THROW(_)     => emit(Opcodes.ATHROW)
            }

          }

        }

      } // end of genCode()'s genBlock()

      /**
       * Emits one or more conversion instructions based on the types given as arguments.
       *
       * @param from The type of the value to be converted into another type.
       * @param to   The type the value will be converted into.
       */
      def emitT2T(from: TypeKind, to: TypeKind) {
        assert(isNonUnitValueTK(from), from)
        assert(isNonUnitValueTK(to),   to)

            def pickOne(opcs: Array[Int]) {
              val chosen = (to: @unchecked) match {
                case BYTE   => opcs(0)
                case SHORT  => opcs(1)
                case CHAR   => opcs(2)
                case INT    => opcs(3)
                case LONG   => opcs(4)
                case FLOAT  => opcs(5)
                case DOUBLE => opcs(6)
              }
              if(chosen != -1) { emit(chosen) }
            }

        if(from == to) { return }
        if((from == BOOL) || (to == BOOL)) {
          // the only conversion involving BOOL that is allowed is (BOOL -> BOOL)
          throw new Error("inconvertible types : " + from.toString() + " -> " + to.toString())
        }

        if(from.isIntSizedType) { // BYTE, CHAR, SHORT, and INT. (we're done with BOOL already)

          val fromByte  = { import asm.Opcodes._; Array( -1,  -1, I2C,  -1, I2L, I2F, I2D) } // do nothing for (BYTE -> SHORT) and for (BYTE -> INT)
          val fromChar  = { import asm.Opcodes._; Array(I2B, I2S,  -1,  -1, I2L, I2F, I2D) } // for (CHAR  -> INT) do nothing
          val fromShort = { import asm.Opcodes._; Array(I2B,  -1, I2C,  -1, I2L, I2F, I2D) } // for (SHORT -> INT) do nothing
          val fromInt   = { import asm.Opcodes._; Array(I2B, I2S, I2C,  -1, I2L, I2F, I2D) }

          (from: @unchecked) match {
            case BYTE  => pickOne(fromByte)
            case SHORT => pickOne(fromShort)
            case CHAR  => pickOne(fromChar)
            case INT   => pickOne(fromInt)
          }

        } else { // FLOAT, LONG, DOUBLE

          (from: @unchecked) match {
            case FLOAT           =>
              import asm.Opcodes.{ F2L, F2D, F2I }
              (to: @unchecked) match {
                case LONG    => emit(F2L)
                case DOUBLE  => emit(F2D)
                case _       => emit(F2I); emitT2T(INT, to)
              }

            case LONG            =>
              import asm.Opcodes.{ L2F, L2D, L2I }
              (to: @unchecked) match {
                case FLOAT   => emit(L2F)
                case DOUBLE  => emit(L2D)
                case _       => emit(L2I); emitT2T(INT, to)
              }

            case DOUBLE          =>
              import asm.Opcodes.{ D2L, D2F, D2I }
              (to: @unchecked) match {
                case FLOAT   => emit(D2F)
                case LONG    => emit(D2L)
                case _       => emit(D2I); emitT2T(INT, to)
              }
          }
        }
      } // end of genCode()'s emitT2T()

      def genPrimitive(primitive: Primitive, pos: Position) {

        import asm.Opcodes;

        primitive match {

          case Negation(kind) => jcode.neg(kind)

          case Arithmetic(op, kind) =>
            op match {

              case ADD => jcode.add(kind)
              case SUB => jcode.sub(kind)
              case MUL => jcode.mul(kind)
              case DIV => jcode.div(kind)
              case REM => jcode.rem(kind)

              case NOT =>
                if(kind.isIntSizedType) {
                  emit(Opcodes.ICONST_M1)
                  emit(Opcodes.IXOR)
                } else if(kind == LONG) {
                  jmethod.visitLdcInsn(new java.lang.Long(-1))
                  jmethod.visitInsn(Opcodes.LXOR)
                } else {
                  abort("Impossible to negate an " + kind)
                }

              case _ =>
                abort("Unknown arithmetic primitive " + primitive)
            }

          // TODO Logical's 2nd elem should be declared ValueTypeKind, to better approximate its allowed values (isIntSized, its comments appears to convey)
          // TODO GenICode uses `toTypeKind` to define that elem, `toValueTypeKind` would be needed instead.
          // TODO How about adding some asserts to Logical and similar ones to capture the remaining constraint (UNIT not allowed).
          case Logical(op, kind) => ((op, kind): @unchecked) match {
            case (AND, LONG) => emit(Opcodes.LAND)
            case (AND, INT)  => emit(Opcodes.IAND)
            case (AND, _)    =>
              emit(Opcodes.IAND)
              if (kind != BOOL) { emitT2T(INT, kind) }

            case (OR, LONG) => emit(Opcodes.LOR)
            case (OR, INT)  => emit(Opcodes.IOR)
            case (OR, _) =>
              emit(Opcodes.IOR)
              if (kind != BOOL) { emitT2T(INT, kind) }

            case (XOR, LONG) => emit(Opcodes.LXOR)
            case (XOR, INT)  => emit(Opcodes.IXOR)
            case (XOR, _) =>
              emit(Opcodes.IXOR)
              if (kind != BOOL) { emitT2T(INT, kind) }
          }

          case Shift(op, kind) => ((op, kind): @unchecked) match {
            case (LSL, LONG) => emit(Opcodes.LSHL)
            case (LSL, INT)  => emit(Opcodes.ISHL)
            case (LSL, _) =>
              emit(Opcodes.ISHL)
              emitT2T(INT, kind)

            case (ASR, LONG) => emit(Opcodes.LSHR)
            case (ASR, INT)  => emit(Opcodes.ISHR)
            case (ASR, _) =>
              emit(Opcodes.ISHR)
              emitT2T(INT, kind)

            case (LSR, LONG) => emit(Opcodes.LUSHR)
            case (LSR, INT)  => emit(Opcodes.IUSHR)
            case (LSR, _) =>
              emit(Opcodes.IUSHR)
              emitT2T(INT, kind)
          }

          case Comparison(op, kind) => ((op, kind): @unchecked) match {
            case (CMP, LONG)    => emit(Opcodes.LCMP)
            case (CMPL, FLOAT)  => emit(Opcodes.FCMPL)
            case (CMPG, FLOAT)  => emit(Opcodes.FCMPG)
            case (CMPL, DOUBLE) => emit(Opcodes.DCMPL)
            case (CMPG, DOUBLE) => emit(Opcodes.DCMPL) // TODO bug? why not DCMPG? http://docs.oracle.com/javase/specs/jvms/se5.0/html/Instructions2.doc3.html
          }

          case Conversion(src, dst) =>
            debuglog("Converting from: " + src + " to: " + dst)
            if (dst == BOOL) { println("Illegal conversion at: " + clasz + " at: " + pos.source + ":" + pos.line) }
            else { emitT2T(src, dst) }

          case ArrayLength(_) => emit(Opcodes.ARRAYLENGTH)

          case StartConcat =>
            jmethod.visitTypeInsn(Opcodes.NEW, StringBuilderClassName)
            jmethod.visitInsn(Opcodes.DUP)
            jcode.invokespecial(
              StringBuilderClassName,
              INSTANCE_CONSTRUCTOR_NAME,
              mdesc_arglessvoid
            )

          case StringConcat(el) =>
            val jtype = el match {
              case REFERENCE(_) | ARRAY(_) => JAVA_LANG_OBJECT
              case _ => javaType(el)
            }
            jcode.invokevirtual(
              StringBuilderClassName,
              "append",
              asm.Type.getMethodDescriptor(StringBuilderType, Array(jtype): _*)
            )

          case EndConcat =>
            jcode.invokevirtual(StringBuilderClassName, "toString", mdesc_toString)

          case _ => abort("Unimplemented primitive " + primitive)
        }
      } // end of genCode()'s genPrimitive()

      // ------------------------------------------------------------------------------------------------------------
      // Part 6 of genCode(): the executable part of genCode() starts here.
      // ------------------------------------------------------------------------------------------------------------

      genBlocks(linearization)

      jmethod.visitLabel(onePastLast)

      if(emitLines) {
        for(LineNumberEntry(line, start) <- lnEntries.sortBy(_.start.getOffset)) { jmethod.visitLineNumber(line, start) }
      }
      if(emitVars)  { genLocalVariableTable() }

    } // end of BytecodeGenerator.genCode()


    ////////////////////// local vars ///////////////////////

    // def sizeOf(sym: Symbol): Int = sizeOf(toTypeKind(sym.tpe))

    def sizeOf(k: TypeKind): Int = if(k.isWideType) 2 else 1

    // def indexOf(m: IMethod, sym: Symbol): Int = {
    //   val Some(local) = m lookupLocal sym
    //   indexOf(local)
    // }

    @inline final def indexOf(local: Local): Int = {
      assert(local.index >= 0, "Invalid index for: " + local + "{" + local.## + "}: ")
      local.index
    }

    /**
     * Compute the indexes of each local variable of the given method.
     * *Does not assume the parameters come first!*
     */
    def computeLocalVarsIndex(m: IMethod) {
      var idx = if (m.symbol.isStaticMember) 0 else 1;

      for (l <- m.params) {
        debuglog("Index value for " + l + "{" + l.## + "}: " + idx)
        l.index = idx
        idx += sizeOf(l.kind)
      }

      for (l <- m.locals if !l.arg) {
        debuglog("Index value for " + l + "{" + l.## + "}: " + idx)
        l.index = idx
        idx += sizeOf(l.kind)
      }
    }

  } // end of class JPlainBuilder

  /** A namespace for utilities to normalize the code of an IMethod, over and beyond what IMethod.normalize() strives for.
   * In particualr, IMethod.normalize() doesn't collapseJumpChains().
   *
   * TODO Eventually, these utilities should be moved to IMethod and reused from normalize() (there's nothing JVM-specific about them).
   */
  object newNormal {

    def startsWithJump(b: BasicBlock): Boolean = { assert(b.nonEmpty, "empty block"); b.firstInstruction.isInstanceOf[JUMP] }

    /** Prune from an exception handler those covered blocks which are jump-only. */
    private def coverWhatCountsOnly(m: IMethod): Boolean = {
      assert(m.hasCode, "code-less method")

      var wasReduced = false
      for(h <- m.exh) {
        val shouldntCover = (h.covered filter startsWithJump)
        if(shouldntCover.nonEmpty) {
          wasReduced = true
          h.covered --= shouldntCover // not removing any block on purpose.
        }
      }

      wasReduced
    }

    /** An exception handler is pruned provided any of the following holds:
     *   (1) it covers nothing (for example, this may result after removing unreachable blocks)
     *   (2) each block it covers is of the form: JUMP(_)
     * Return true iff one or more ExceptionHandlers were removed.
     *
     * A caveat: removing an exception handler, for whatever reason, means that its handler code (even if unreachable)
     * won't be able to cause a class-loading-exception. As a result, behavior can be different.
     */
    private def elimNonCoveringExh(m: IMethod): Boolean = {
      assert(m.hasCode, "code-less method")

        def isRedundant(eh: ExceptionHandler): Boolean = {
          (eh.cls != NoSymbol) && ( // TODO `eh.isFinallyBlock` more readable than `eh.cls != NoSymbol`
                eh.covered.isEmpty
            || (eh.covered forall startsWithJump)
          )
        }

      var wasReduced = false
      val toPrune = (m.exh.toSet filter isRedundant)
      if(toPrune.nonEmpty) {
        wasReduced = true
        for(h <- toPrune; r <- h.blocks) { m.code.removeBlock(r) } // TODO m.code.removeExh(h)
        m.exh = (m.exh filterNot toPrune)
      }

      wasReduced
    }

    private def isJumpOnly(b: BasicBlock): Option[BasicBlock] = {
      b.toList match {
        case JUMP(whereto) :: rest =>
          assert(rest.isEmpty, "A block contains instructions after JUMP (looks like enterIgnoreMode() was itself ignored.)")
          Some(whereto)
        case _ => None
      }
    }

    private def directSuccStar(b: BasicBlock): List[BasicBlock] = { directSuccStar(List(b)) }

    /** Transitive closure of successors potentially reachable due to normal (non-exceptional) control flow.
       Those BBs in the argument are also included in the result */
    private def directSuccStar(starters: Traversable[BasicBlock]): List[BasicBlock] = {
      val result = new mutable.ListBuffer[BasicBlock]
      var toVisit: List[BasicBlock] = starters.toList.distinct
      while(toVisit.nonEmpty) {
        val h   = toVisit.head
        toVisit = toVisit.tail
        result += h
        for(p <- h.directSuccessors; if !result.contains(p) && !toVisit.contains(p)) { toVisit = p :: toVisit }
      }
      result.toList
    }

    /** Returns:
     *  for single-block self-loops, the pair (start, Nil)
     *  for other cycles,            the pair (backedge-target, basic-blocks-in-the-cycle-except-backedge-target)
     *  otherwise a pair consisting of:
     *    (a) the endpoint of a (single or multi-hop) chain of JUMPs
     *        (such endpoint does not start with a JUMP and therefore is not part of the chain); and
     *    (b) the chain (ie blocks to be removed when collapsing the chain of jumps).
     *  Precondition: the BasicBlock given as argument starts with an unconditional JUMP.
     */
    private def finalDestination(start: BasicBlock): (BasicBlock, List[BasicBlock]) = {
      assert(startsWithJump(start), "not the start of a (single or multi-hop) chain of JUMPs.")
      var hops: List[BasicBlock] = Nil
      var prev = start
      var done = false
      do {
        done = isJumpOnly(prev) match {
          case Some(dest) =>
            if (dest == start) { return (start, hops) } // leave infinite-loops in place
            hops ::= prev
            if (hops.contains(dest)) {
              // leave infinite-loops in place
              return (dest, hops filterNot (dest eq))
            }
            prev = dest;
            false
          case None => true
        }
      } while(!done)

      (prev, hops)
    }

    /**
     * Collapse a chain of "jump-only" blocks such as:
     *
     *      JUMP b1;
     *  b1: JUMP b2;
     *  b2: JUMP ... etc.
     *
     *  by re-wiring predecessors to target directly the "final destination".
     *  Even if covered by an exception handler, a "non-self-loop jump-only block" can always be removed.

     *  Returns true if any replacement was made, false otherwise.
     *
     *  In more detail:
     *    Starting at each of the entry points (m.startBlock, the start block of each exception handler)
     *    rephrase those control-flow instructions targeting a jump-only block (which jumps to a final destination D) to target D.
     *    The blocks thus skipped are also removed from IMethod.blocks.
     *
     *  Rationale for this normalization:
     *    test/files/run/private-inline.scala after -optimize is chock full of
     *    BasicBlocks containing just JUMP(whereTo), where no exception handler straddles them.
     *    They should be collapsed by IMethod.normalize() but aren't.
     *    That was fine in FJBG times when by the time the exception table was emitted,
     *    it already contained "anchored" labels (ie instruction offsets were known)
     *    and thus ranges with identical (start, end) (i.e, identical after GenJVM omitted the JUMPs in question)
     *    could be weeded out to avoid "java.lang.ClassFormatError: Illegal exception table range"
     *    Now that visitTryCatchBlock() must be called before Labels are resolved,
     *    this method gets rid of the BasicBlocks described above (to recap, consisting of just a JUMP).
     */
    private def collapseJumpOnlyBlocks(m: IMethod): Boolean = {
      assert(m.hasCode, "code-less method")

          /* "start" is relative in a cycle, but we call this helper with the "first" entry-point we found. */
          def realTarget(jumpStart: BasicBlock): Map[BasicBlock, BasicBlock] = {
            assert(startsWithJump(jumpStart), "not part of a jump-chain")
            val Pair(dest, redundants) = finalDestination(jumpStart)
            (for(skipOver <- redundants) yield Pair(skipOver, dest)).toMap
          }

          def rephraseGotos(detour: Map[BasicBlock, BasicBlock]) {
            for(Pair(oldTarget, newTarget) <- detour.iterator) {
              if(m.startBlock == oldTarget) {
                m.code.startBlock = newTarget
              }
              for(eh <- m.exh; if eh.startBlock == oldTarget) {
                eh.setStartBlock(newTarget)
              }
              for(b <- m.blocks; if !detour.isDefinedAt(b)) {
                val idxLast = (b.size - 1)
                b.lastInstruction match {
                  case JUMP(whereto) =>
                    if (whereto == oldTarget) {
                      b.replaceInstruction(idxLast, JUMP(newTarget))
                    }
                  case CJUMP(succ, fail, cond, kind) =>
                    if ((succ == oldTarget) || (fail == oldTarget)) {
                      b.replaceInstruction(idxLast, CJUMP(detour.getOrElse(succ, succ),
                                                          detour.getOrElse(fail, fail),
                                                          cond, kind))
                    }
                  case CZJUMP(succ, fail, cond, kind) =>
                    if ((succ == oldTarget) || (fail == oldTarget)) {
                      b.replaceInstruction(idxLast, CZJUMP(detour.getOrElse(succ, succ),
                                                           detour.getOrElse(fail, fail),
                                                           cond, kind))
                    }
                  case SWITCH(tags, labels) =>
                    if(labels exists (detour.isDefinedAt(_))) {
                      val newLabels = (labels map { lab => detour.getOrElse(lab, lab) })
                      b.replaceInstruction(idxLast, SWITCH(tags, newLabels))
                    }
                  case _ => ()
                }
              }
            }
          }

          /* remove from all containers that may contain a reference to */
          def elide(redu: BasicBlock) {
            assert(m.startBlock != redu, "startBlock should have been re-wired by now")
            m.code.removeBlock(redu);
          }

      var wasReduced = false
      val entryPoints: List[BasicBlock] = m.startBlock :: (m.exh map (_.startBlock));

      var elided     = mutable.Set.empty[BasicBlock] // debug
      var newTargets = mutable.Set.empty[BasicBlock] // debug

      for (ep <- entryPoints) {
        var reachable = directSuccStar(ep) // this list may contain blocks belonging to jump-chains that we'll skip over
        while(reachable.nonEmpty) {
          val h = reachable.head
          reachable = reachable.tail
          if(startsWithJump(h)) {
            val detour = realTarget(h)
            if(detour.nonEmpty) {
              wasReduced = true
              reachable = (reachable filterNot (detour.keySet.contains(_)))
              rephraseGotos(detour)
              detour.keySet foreach elide
              elided     ++= detour.keySet
              newTargets ++= detour.values
            }
          }
        }
      }
      assert(newTargets.intersect(elided).isEmpty, "contradiction: we just elided the final destionation of a jump-chain")

      wasReduced
    }

    def normalize(m: IMethod) {
      if(!m.hasCode) { return }
      collapseJumpOnlyBlocks(m)
      var wasReduced = false;
      do {
        wasReduced = false
        // Prune from an exception handler those covered blocks which are jump-only.
        wasReduced |= coverWhatCountsOnly(m); icodes.checkValid(m) // TODO should be unnecessary now that collapseJumpOnlyBlocks(m) is in place
        // Prune exception handlers covering nothing.
        wasReduced |= elimNonCoveringExh(m);  icodes.checkValid(m)

        // TODO see note in genExceptionHandlers about an ExceptionHandler.covered containing dead blocks (newNormal should remove them, but, where do those blocks come from?)
      } while (wasReduced)

      // TODO this would be a good time to remove synthetic local vars seeing no use, don't forget to call computeLocalVarsIndex() afterwards.
    }

  }

}
