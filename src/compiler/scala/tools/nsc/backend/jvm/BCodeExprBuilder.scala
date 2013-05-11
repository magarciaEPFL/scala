/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala
package tools.nsc
package backend
package jvm

import scala.collection.{ mutable, immutable }
import scala.tools.nsc.symtab._
import scala.annotation.switch

import scala.tools.asm

abstract class BCodeExprBuilder extends BCodeBuilder {
  import global._
  import definitions._

  /*
   *
   *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
   *  @version 1.0
   *
   */
  final class PlainClassBuilder(cunit: CompilationUnit) extends PlainBaseBuilder(cunit) {

    import icodes.TestOp
    import icodes.opcodes.InvokeStyle

    override def getCurrentCUnit(): CompilationUnit = { cunit }

    /*  If the selector type has a member with the right name,
     *  it is the host class; otherwise the symbol's owner.
     */
    def findHostClass(selector: Type, sym: Symbol) = selector member sym.name match {
      case NoSymbol   => log(s"Rejecting $selector as host class for $sym") ; sym.owner
      case _          => selector.typeSymbol
    }

    /* ---------------- helper utils for generating methods and code ---------------- */

    def emit(opc: Int) { mnode.visitInsn(opc) }
    def emit(i: asm.tree.AbstractInsnNode) { mnode.instructions.add(i) }
    def emit(is: List[asm.tree.AbstractInsnNode]) { for(i <- is) { mnode.instructions.add(i) } }

    def emitZeroOf(tk: BType) {
      (tk.sort: @switch) match {
        case asm.Type.BOOLEAN => bc.boolconst(false)
        case asm.Type.BYTE  |
             asm.Type.SHORT |
             asm.Type.CHAR  |
             asm.Type.INT     => bc.iconst(0)
        case asm.Type.LONG    => bc.lconst(0)
        case asm.Type.FLOAT   => bc.fconst(0)
        case asm.Type.DOUBLE  => bc.dconst(0)
        case asm.Type.VOID    => ()
        case _ => emit(asm.Opcodes.ACONST_NULL)
      }
    }

    /*
     * Emits code that adds nothing to the operand stack.
     * Two main cases: `tree` is an assignment,
     * otherwise an `adapt()` to UNIT is performed if needed.
     */
    def genStat(tree: Tree) {
      lineNumber(tree)
      tree match {
        case Assign(lhs @ Select(_, _), rhs) =>
          val isStatic = lhs.symbol.isStaticMember
          if (!isStatic) { genLoadQualifier(lhs) }
          genLoad(rhs, symInfoTK(lhs.symbol))
          lineNumber(tree)
          fieldStore(lhs.symbol)

        case Assign(lhs, rhs) =>
          val s = lhs.symbol
          val Local(tk, _, idx, _) = locals.getOrElse(s, makeLocal(s))
          genLoad(rhs, tk)
          lineNumber(tree)
          bc.store(idx, tk)

        case _ =>
          genLoad(tree, UNIT)
      }
    }

    def genThrow(expr: Tree): BType = {
      val thrownKind = tpeTK(expr)
      assert(exemplars.get(thrownKind).isSubtypeOf(ThrowableReference))
      genLoad(expr, thrownKind)
      lineNumber(expr)
      emit(asm.Opcodes.ATHROW) // ICode enters here into enterIgnoreMode, we'll rely instead on DCE at ClassNode level.

      RT_NOTHING // always returns the same, the invoker should know :)
    }

    /* Generate code for primitive arithmetic operations. */
    def genArithmeticOp(tree: Tree, code: Int): BType = {
      val Apply(fun @ Select(larg, _), args) = tree
      var resKind = tpeTK(larg)

      assert(args.length <= 1, "Too many arguments for primitive function: " + fun.symbol)
      assert(resKind.isNumericType || (resKind == BOOL),
             resKind.toString + " is not a numeric or boolean type " + "[operation: " + fun.symbol + "]")

      args match {
        // unary operation
        case Nil =>
          genLoad(larg, resKind)
          code match {
            case scalaPrimitives.POS => () // nothing
            case scalaPrimitives.NEG => bc.neg(resKind)
            case scalaPrimitives.NOT => bc.genPrimitiveArithmetic(icodes.NOT, resKind)
            case _ => abort("Unknown unary operation: " + fun.symbol.fullName + " code: " + code)
          }

        // binary operation
        case rarg :: Nil =>
          resKind = maxType(tpeTK(larg), tpeTK(rarg))
          if (scalaPrimitives.isShiftOp(code) || scalaPrimitives.isBitwiseOp(code)) {
            assert(resKind.isIntegralType || (resKind == BOOL),
                   resKind.toString + " incompatible with arithmetic modulo operation.")
          }

          genLoad(larg, resKind)
          genLoad(rarg, // check .NET size of shift arguments!
                  if (scalaPrimitives.isShiftOp(code)) INT else resKind)

          (code: @switch) match {
            case scalaPrimitives.ADD => bc add resKind
            case scalaPrimitives.SUB => bc sub resKind
            case scalaPrimitives.MUL => bc mul resKind
            case scalaPrimitives.DIV => bc div resKind
            case scalaPrimitives.MOD => bc rem resKind

            case scalaPrimitives.OR  |
                 scalaPrimitives.XOR |
                 scalaPrimitives.AND => bc.genPrimitiveLogical(code, resKind)

            case scalaPrimitives.LSL |
                 scalaPrimitives.LSR |
                 scalaPrimitives.ASR => bc.genPrimitiveShift(code, resKind)

            case _                   => abort("Unknown primitive: " + fun.symbol + "[" + code + "]")
          }

        case _ =>
          abort("Too many arguments for primitive function: " + tree)
      }
      lineNumber(tree)
      resKind
    }

    /* Generate primitive array operations. */
    def genArrayOp(tree: Tree, code: Int, expectedType: BType): BType = {
      val Apply(Select(arrayObj, _), args) = tree
      val k = tpeTK(arrayObj)
      genLoad(arrayObj, k)
      val elementType = typeOfArrayOp.getOrElse(code, abort("Unknown operation on arrays: " + tree + " code: " + code))

      var generatedType = expectedType

      if (scalaPrimitives.isArrayGet(code)) {
        // load argument on stack
        assert(args.length == 1, "Too many arguments for array get operation: " + tree);
        genLoad(args.head, INT)
        generatedType = k.getComponentType
        bc.aload(elementType)
      }
      else if (scalaPrimitives.isArraySet(code)) {
        assert(args.length == 2, "Too many arguments for array set operation: " + tree);
        genLoad(args.head, INT)
        genLoad(args.tail.head, tpeTK(args.tail.head))
        // the following line should really be here, but because of bugs in erasure
        // we pretend we generate whatever type is expected from us.
        //generatedType = UNIT
        bc.astore(elementType)
      }
      else {
        generatedType = INT
        emit(asm.Opcodes.ARRAYLENGTH)
      }
      lineNumber(tree)

      generatedType
    }

    def genSynchronized(tree: Apply, expectedType: BType): BType = {
      val Apply(fun, args) = tree
      val monitor = makeLocal(ObjectReference, "monitor")
      val monCleanup = new asm.Label

      // if the synchronized block returns a result, store it in a local variable.
      // Just leaving it on the stack is not valid in MSIL (stack is cleaned when leaving try-blocks).
      val hasResult = (expectedType != UNIT)
      val monitorResult: Symbol = if (hasResult) makeLocal(tpeTK(args.head), "monitorResult") else null;

      /* ------ (1) pushing and entering the monitor, also keeping a reference to it in a local var. ------ */
      genLoadQualifier(fun)
      bc dup ObjectReference
      store(monitor)
      emit(asm.Opcodes.MONITORENTER)

      /* ------ (2) Synchronized block.
       *            Reached by fall-through from (1).
       *            Protected by:
       *            (2.a) the EH-version of the monitor-exit, and
       *            (2.b) whatever protects the whole synchronized expression.
       * ------
       */
      val startProtected = currProgramPoint()
      registerCleanup(monCleanup)
      genLoad(args.head, expectedType /* toTypeKind(tree.tpe.resultType) */)
      unregisterCleanup(monCleanup)
      if (hasResult) { store(monitorResult) }
      nopIfNeeded(startProtected)
      val endProtected = currProgramPoint()

      /* ------ (3) monitor-exit after normal, non-early-return, termination of (2).
       *            Reached by fall-through from (2).
       *            Protected by whatever protects the whole synchronized expression.
       * ------
       */
      load(monitor)
      emit(asm.Opcodes.MONITOREXIT)
      if (hasResult) { load(monitorResult) }
      val postHandler = new asm.Label
      bc goTo postHandler

      /* ------ (4) exception-handler version of monitor-exit code.
       *            Reached upon abrupt termination of (2).
       *            Protected by whatever protects the whole synchronized expression.
       * ------
       */
      protect(startProtected, endProtected, currProgramPoint(), ThrowableReference)
      load(monitor)
      emit(asm.Opcodes.MONITOREXIT)
      emit(asm.Opcodes.ATHROW)

      /* ------ (5) cleanup version of monitor-exit code.
       *            Reached upon early-return from (2).
       *            Protected by whatever protects the whole synchronized expression.
       * ------
       */
      if (shouldEmitCleanup) {
        markProgramPoint(monCleanup)
        load(monitor)
        emit(asm.Opcodes.MONITOREXIT)
        pendingCleanups()
      }

      /* ------ (6) normal exit of the synchronized expression.
       *            Reached after normal, non-early-return, termination of (3).
       *            Protected by whatever protects the whole synchronized expression.
       * ------
       */
      mnode visitLabel postHandler

      lineNumber(tree)

      expectedType
    }

    def genLoadIf(tree: If, expectedType: BType): BType = {
      val If(condp, thenp, elsep) = tree

      val success = new asm.Label
      val failure = new asm.Label

      val hasElse = !elsep.isEmpty
      val postIf  = if (hasElse) new asm.Label else failure

      genCond(condp, success, failure)

      val thenKind      = tpeTK(thenp)
      val elseKind      = if (!hasElse) UNIT else tpeTK(elsep)
      def hasUnitBranch = (thenKind == UNIT || elseKind == UNIT)
      val resKind       = if (hasUnitBranch) UNIT else tpeTK(tree)

      markProgramPoint(success)
      genLoad(thenp, resKind)
      if (hasElse) { bc goTo postIf }
      markProgramPoint(failure)
      if (hasElse) {
        genLoad(elsep, resKind)
        markProgramPoint(postIf)
      }

      resKind
    }

    /*
     *  Detects whether no instructions have been emitted since label `lbl` and if so emits a NOP.
     *  Useful to avoid emitting an empty try-block being protected by exception handlers,
     *  which results in "java.lang.ClassFormatError: Illegal exception table range". See SI-6102.
     */
    def nopIfNeeded(lbl: asm.Label) {
      val noInstructionEmitted = isAtProgramPoint(lbl)
      if (noInstructionEmitted) { emit(asm.Opcodes.NOP) }
    }

    /*
     *  Emitting try-catch is easy, emitting try-catch-finally not quite so.
     *  A finally-block (which always has type Unit, thus leaving the operand stack unchanged)
     *  affects control-transfer from protected regions, as follows:
     *
     *    (a) `return` statement:
     *
     *        First, the value to return (if any) is evaluated.
     *        Afterwards, all enclosing finally-blocks are run, from innermost to outermost.
     *        Only then is the return value (if any) returned.
     *
     *        Some terminology:
     *          (a.1) Executing a return statement that is protected
     *                by one or more finally-blocks is called "early return"
     *          (a.2) the chain of code sections (a code section for each enclosing finally-block)
     *                to run upon early returns is called "cleanup chain"
     *
     *        As an additional spin, consider a return statement in a finally-block.
     *        In this case, the value to return depends on how control arrived at that statement:
     *        in case it arrived via a previous return, the previous return enjoys priority:
     *        the value to return is given by that statement.
     *
     *    (b) A finally-block protects both the try-clause and the catch-clauses.
     *
     *           Sidenote:
     *             A try-clause may contain an empty block. On CLR, a finally-block has special semantics
     *             regarding Abort interruptions; but on the JVM it's safe to elide an exception-handler
     *             that protects an "empty" range ("empty" as in "containing NOPs only",
     *             see `asm.optimiz.DanglingExcHandlers` and SI-6720).
     *
     *        This means a finally-block indicates instructions that can be reached:
     *          (b.1) Upon normal (non-early-returning) completion of the try-clause or a catch-clause
     *                In this case, the next-program-point is that following the try-catch-finally expression.
     *          (b.2) Upon early-return initiated in the try-clause or a catch-clause
     *                In this case, the next-program-point is the enclosing cleanup section (if any), otherwise return.
     *          (b.3) Upon abrupt termination (due to unhandled exception) of the try-clause or a catch-clause
     *                In this case, the unhandled exception must be re-thrown after running the finally-block.
     *
     *    (c) finally-blocks are implicit to `synchronized` (a finally-block is added to just release the lock)
     *        that's why `genSynchronized()` too emits cleanup-sections.
     *
     *  A number of code patterns can be emitted to realize the intended semantics.
     *
     *  A popular alternative (GenICode, javac) consists in duplicating the cleanup-chain at each early-return position.
     *  The principle at work being that once control is transferred to a cleanup-section,
     *  control will always stay within the cleanup-chain.
     *  That is, barring an exception being thrown in a cleanup-section, in which case the enclosing try-block
     *  (reached via abrupt termination) takes over.
     *
     *  The observations above hint at another code layout, less verbose, for the cleanup-chain.
     *
     *  The code layout that GenBCode emits takes into account that once a cleanup section has been reached,
     *  jumping to the next cleanup-section (and so on, until the outermost one) realizes the correct semantics.
     *
     *  There is still code duplication in that two cleanup-chains are needed (but this is unavoidable, anyway):
     *  one for normal control flow and another chain consisting of exception handlers.
     *  The in-line comments below refer to them as
     *    - "early-return-cleanups" and
     *    - "exception-handler-version-of-finally-block" respectively.
     *
     */
    def genLoadTry(tree: Try): BType = {

      val Try(block, catches, finalizer) = tree
      val kind = tpeTK(tree)

      val caseHandlers: List[EHClause] =
        for (CaseDef(pat, _, caseBody) <- catches) yield {
          pat match {
            case Typed(Ident(nme.WILDCARD), tpt)  => NamelessEH(tpeTK(tpt), caseBody)
            case Ident(nme.WILDCARD)              => NamelessEH(ThrowableReference,  caseBody)
            case Bind(_, _)                       => BoundEH   (pat.symbol, caseBody)
          }
        }

      // ------ (0) locals used later ------

      /*
       * `postHandlers` is a program point denoting:
       *     (a) the finally-clause conceptually reached via fall-through from try-catch-finally
       *         (in case a finally-block is present); or
       *     (b) the program point right after the try-catch
       *         (in case there's no finally-block).
       * The name choice emphasizes that the code section lies "after all exception handlers",
       * where "all exception handlers" includes those derived from catch-clauses as well as from finally-blocks.
       */
      val postHandlers = new asm.Label

      val hasFinally   = (finalizer != EmptyTree)

      /*
       * used in the finally-clause reached via fall-through from try-catch, if any.
       */
      val guardResult  = hasFinally && (kind != UNIT) && mayCleanStack(finalizer)

      /*
       * please notice `tmp` has type tree.tpe, while `earlyReturnVar` has the method return type.
       * Because those two types can be different, dedicated vars are needed.
       */
      val tmp          = if (guardResult) makeLocal(tpeTK(tree), "tmp") else null;

      /*
       * upon early return from the try-body or one of its EHs (but not the EH-version of the finally-clause)
       * AND hasFinally, a cleanup is needed.
       */
      val finCleanup   = if (hasFinally) new asm.Label else null

      /* ------ (1) try-block, protected by:
       *                       (1.a) the EHs due to case-clauses,   emitted in (2),
       *                       (1.b) the EH  due to finally-clause, emitted in (3.A)
       *                       (1.c) whatever protects the whole try-catch-finally expression.
       * ------
       */

      val startTryBody = currProgramPoint()
      registerCleanup(finCleanup)
      genLoad(block, kind)
      unregisterCleanup(finCleanup)
      nopIfNeeded(startTryBody)
      val endTryBody = currProgramPoint()
      bc goTo postHandlers

      /* ------ (2) One EH for each case-clause (this does not include the EH-version of the finally-clause)
       *            An EH in (2) is reached upon abrupt termination of (1).
       *            An EH in (2) is protected by:
       *                         (2.a) the EH-version of the finally-clause, if any.
       *                         (2.b) whatever protects the whole try-catch-finally expression.
       * ------
       */

      for (ch <- caseHandlers) {

        // (2.a) emit case clause proper
        val startHandler = currProgramPoint()
        var endHandler: asm.Label = null
        var excType: BType = null
        registerCleanup(finCleanup)
        ch match {
          case NamelessEH(typeToDrop, caseBody) =>
            bc drop typeToDrop
            genLoad(caseBody, kind) // adapts caseBody to `kind`, thus it can be stored, if `guardResult`, in `tmp`.
            nopIfNeeded(startHandler)
            endHandler = currProgramPoint()
            excType = typeToDrop

          case BoundEH   (patSymbol,  caseBody) =>
            // test/files/run/contrib674.scala , a local-var already exists for patSymbol.
            // rather than creating on first-access, we do it right away to emit debug-info for the created local var.
            val Local(patTK, _, patIdx, _) = locals.getOrElse(patSymbol, makeLocal(patSymbol))
            bc.store(patIdx, patTK)
            genLoad(caseBody, kind)
            nopIfNeeded(startHandler)
            endHandler = currProgramPoint()
            emitLocalVarScope(patSymbol, startHandler, endHandler)
            excType = patTK
        }
        unregisterCleanup(finCleanup)
        // (2.b)  mark the try-body as protected by this case clause.
        protect(startTryBody, endTryBody, startHandler, excType)
        // (2.c) emit jump to the program point where the finally-clause-for-normal-exit starts, or in effect `after` if no finally-clause was given.
        bc goTo postHandlers

      }

      /* ------ (3.A) The exception-handler-version of the finally-clause.
       *              Reached upon abrupt termination of (1) or one of the EHs in (2).
       *              Protected only by whatever protects the whole try-catch-finally expression.
       * ------
       */

      // a note on terminology: this is not "postHandlers", despite appearences.
      // "postHandlers" as in the source-code view. And from that perspective, both (3.A) and (3.B) are invisible implementation artifacts.
      if (hasFinally) {
        nopIfNeeded(startTryBody)
        val finalHandler = currProgramPoint() // version of the finally-clause reached via unhandled exception.
        protect(startTryBody, finalHandler, finalHandler, null)
        val Local(eTK, _, eIdx, _) = locals(makeLocal(ThrowableReference, "exc"))
        bc.store(eIdx, eTK)
        emitFinalizer(finalizer, null, isDuplicate = true)
        bc.load(eIdx, eTK)
        emit(asm.Opcodes.ATHROW)
      }

      /* ------ (3.B) Cleanup-version of the finally-clause.
       *              Reached upon early RETURN from (1) or upon early RETURN from one of the EHs in (2)
       *              (and only from there, ie reached only upon early RETURN from
       *               program regions bracketed by registerCleanup/unregisterCleanup).
       *              Protected only by whatever protects the whole try-catch-finally expression.
       *
       *              Given that control arrives to a cleanup section only upon early RETURN,
       *              the value to return (if any) is always available. Therefore, a further RETURN
       *              found in a cleanup section is always ignored (a warning is displayed, @see `genReturn()`).
       *              In order for `genReturn()` to know whether the return statement is enclosed in a cleanup section,
       *              the variable `insideCleanupBlock` is used.
       * ------
       */

      // this is not "postHandlers" either.
      // `shouldEmitCleanup` can be set, and at the same time this try expression may lack a finally-clause.
      // In other words, all combinations of (hasFinally, shouldEmitCleanup) are valid.
      if (hasFinally && shouldEmitCleanup) {
        val savedInsideCleanup = insideCleanupBlock
        insideCleanupBlock = true
        markProgramPoint(finCleanup)
        // regarding return value, the protocol is: in place of a `return-stmt`, a sequence of `adapt, store, jump` are inserted.
        emitFinalizer(finalizer, null, isDuplicate = true)
        pendingCleanups()
        insideCleanupBlock = savedInsideCleanup
      }

      /* ------ (4) finally-clause-for-normal-nonEarlyReturn-exit
       *            Reached upon normal, non-early-return termination of (1) or of an EH in (2).
       *            Protected only by whatever protects the whole try-catch-finally expression.
       * TODO explain what happens upon RETURN contained in (4)
       * ------
       */

      markProgramPoint(postHandlers)
      if (hasFinally) {
        emitFinalizer(finalizer, tmp, isDuplicate = false) // the only invocation of emitFinalizer with `isDuplicate == false`
      }

      kind
    } // end of genLoadTry()

    /* if no more pending cleanups, all that remains to do is return. Otherwise jump to the next (outer) pending cleanup. */
    private def pendingCleanups() {
      cleanups match {
        case Nil =>
          if (earlyReturnVar != null) {
            load(earlyReturnVar)
            bc.emitRETURN(locals(earlyReturnVar).tk)
          } else {
            bc emitRETURN UNIT
          }
          shouldEmitCleanup = false

        case nextCleanup :: _ =>
          bc goTo nextCleanup
      }
    }

    private def protect(start: asm.Label, end: asm.Label, handler: asm.Label, excType: BType) {
      val excInternalName: String =
        if (excType == null) null
        else excType.getInternalName
      assert(start != end, "protecting a range of zero instructions leads to illegal class format. Solution: add a NOP to that range.")
      mnode.visitTryCatchBlock(start, end, handler, excInternalName)
    }

    /* `tmp` (if non-null) is the symbol of the local-var used to preserve the result of the try-body, see `guardResult` */
    private def emitFinalizer(finalizer: Tree, tmp: Symbol, isDuplicate: Boolean) {
      var saved: immutable.Map[ /* LabelDef */ Symbol, asm.Label ] = null
      if (isDuplicate) {
        saved = jumpDest
        for(ldef <- labelDefsAtOrUnder(finalizer)) {
          jumpDest -= ldef.symbol
        }
      }
      // when duplicating, the above guarantees new asm.Labels are used for LabelDefs contained in the finalizer (their vars are reused, that's ok)
      if (tmp != null) { store(tmp) }
      genLoad(finalizer, UNIT)
      if (tmp != null) { load(tmp)  }
      if (isDuplicate) {
        jumpDest = saved
      }
    }

    def genPrimitiveOp(tree: Apply, expectedType: BType): BType = {
      val sym = tree.symbol
      val Apply(fun @ Select(receiver, _), _) = tree
      val code = scalaPrimitives.getPrimitive(sym, receiver.tpe)

      import scalaPrimitives.{isArithmeticOp, isArrayOp, isLogicalOp, isComparisonOp}

      if (isArithmeticOp(code))                genArithmeticOp(tree, code)
      else if (code == scalaPrimitives.CONCAT) genStringConcat(tree)
      else if (code == scalaPrimitives.HASH)   genScalaHash(receiver)
      else if (isArrayOp(code))                genArrayOp(tree, code, expectedType)
      else if (isLogicalOp(code) || isComparisonOp(code)) {
        val success, failure, after = new asm.Label
        genCond(tree, success, failure)
        // success block
          markProgramPoint(success)
          bc boolconst true
          bc goTo after
        // failure block
          markProgramPoint(failure)
          bc boolconst false
        // after
        markProgramPoint(after)

        BOOL
      }
      else if (code == scalaPrimitives.SYNCHRONIZED)
        genSynchronized(tree, expectedType)
      else if (scalaPrimitives.isCoercion(code)) {
        genLoad(receiver, tpeTK(receiver))
        lineNumber(tree)
        genCoercion(code)
        coercionTo(code)
      }
      else abort(
        "Primitive operation not handled yet: " + sym.fullName + "(" +
        fun.symbol.simpleName + ") " + " at: " + (tree.pos)
      )
    }

    /* Generate code for trees that produce values on the stack */
    def genLoad(tree: Tree, expectedType: BType) {
      var generatedType = expectedType

      lineNumber(tree)

      tree match {
        case lblDf : LabelDef => genLabelDef(lblDf, expectedType)

        case ValDef(_, nme.THIS, _, _) =>
          debuglog("skipping trivial assign to _$this: " + tree)

        case ValDef(_, _, _, rhs) =>
          val sym = tree.symbol
          /* most of the time, !locals.contains(sym), unless the current activation of genLoad() is being called
             while duplicating a finalizer that contains this ValDef. */
          val Local(tk, _, idx, isSynth) = locals.getOrElseUpdate(sym, makeLocal(sym))
          if (rhs == EmptyTree) { emitZeroOf(tk) }
          else { genLoad(rhs, tk) }
          bc.store(idx, tk)
          if (!isSynth) { // there are case <synthetic> ValDef's emitted by patmat
            varsInScope ::= (sym -> currProgramPoint())
          }
          generatedType = UNIT

        case t : If =>
          generatedType = genLoadIf(t, expectedType)

        case r : Return =>
          genReturn(r)
          generatedType = expectedType

        case t : Try =>
          generatedType = genLoadTry(t)

        case Throw(expr) =>
          generatedType = genThrow(expr)

        case New(tpt) =>
          abort("Unexpected New(" + tpt.summaryString + "/" + tpt + ") reached GenBCode.\n" +
                "  Call was genLoad" + ((tree, expectedType)))

        case app : Apply =>
          generatedType = genApply(app, expectedType)

        case ApplyDynamic(qual, args) => sys.error("No invokedynamic support yet.")

        case This(qual) =>
          val symIsModuleClass = tree.symbol.isModuleClass
          assert(tree.symbol == claszSymbol || symIsModuleClass,
                 "Trying to access the this of another class: " +
                 "tree.symbol = " + tree.symbol + ", class symbol = " + claszSymbol + " compilation unit:"+ cunit)
          if (symIsModuleClass && tree.symbol != claszSymbol) {
            generatedType = genLoadModule(tree)
          }
          else {
            mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
            generatedType =
              if (tree.symbol == ArrayClass) ObjectReference
              else brefType(thisName) // inner class (if any) for claszSymbol already tracked.
          }

        case Select(Ident(nme.EMPTY_PACKAGE_NAME), module) =>
          assert(tree.symbol.isModule, "Selection of non-module from empty package: " + tree + " sym: " + tree.symbol + " at: " + (tree.pos))
          genLoadModule(tree)

        case Select(qualifier, selector) =>
          val sym = tree.symbol
          generatedType = symInfoTK(sym)
          val hostClass = findHostClass(qualifier.tpe, sym)
          log(s"Host class of $sym with qual $qualifier (${qualifier.tpe}) is $hostClass")
          val qualSafeToElide = treeInfo isQualifierSafeToElide qualifier

          def genLoadQualUnlessElidable() { if (!qualSafeToElide) { genLoadQualifier(tree) } }

          if (sym.isModule) {
            genLoadQualUnlessElidable()
            genLoadModule(tree)
          }
          else if (sym.isStaticMember) {
            genLoadQualUnlessElidable()
            fieldLoad(sym, hostClass)
          }
          else {
            genLoadQualifier(tree)
            fieldLoad(sym, hostClass)
          }

        case Ident(name) =>
          val sym = tree.symbol
          if (!sym.isPackage) {
            val tk = symInfoTK(sym)
            if (sym.isModule) { genLoadModule(tree) }
            else { load(sym) }
            generatedType = tk
          }

        case Literal(value) =>
          if (value.tag != UnitTag) (value.tag, expectedType) match {
            case (IntTag,   LONG  ) => bc.lconst(value.longValue);       generatedType = LONG
            case (FloatTag, DOUBLE) => bc.dconst(value.doubleValue);     generatedType = DOUBLE
            case (NullTag,  _     ) => bc.emit(asm.Opcodes.ACONST_NULL); generatedType = RT_NULL
            case _                  => genConstant(value);               generatedType = tpeTK(tree)
          }

        case blck : Block => genBlock(blck, expectedType)

        case Typed(Super(_, _), _) => genLoad(This(claszSymbol), expectedType)

        case Typed(expr, _) => genLoad(expr, expectedType)

        case Assign(_, _) =>
          generatedType = UNIT
          genStat(tree)

        case av : ArrayValue =>
          generatedType = genArrayValue(av)

        case mtch : Match =>
          generatedType = genMatch(mtch)

        case EmptyTree => if (expectedType != UNIT) { emitZeroOf(expectedType) }

        case _ => abort("Unexpected tree in genLoad: " + tree + "/" + tree.getClass + " at: " + tree.pos)
      }

      // emit conversion
      if (generatedType != expectedType) {
        adapt(generatedType, expectedType)
      }

    } // end of GenBCode.genLoad()

    // ---------------- field load and store ----------------

    /*
     * must-single-thread
     */
    def fieldLoad( field: Symbol, hostClass: Symbol = null) {
      fieldOp(field, isLoad = true,  hostClass)
    }
    /*
     * must-single-thread
     */
    def fieldStore(field: Symbol, hostClass: Symbol = null) {
      fieldOp(field, isLoad = false, hostClass)
    }

    /*
     * must-single-thread
     */
    private def fieldOp(field: Symbol, isLoad: Boolean, hostClass: Symbol = null) {
      // LOAD_FIELD.hostClass , CALL_METHOD.hostClass , and #4283
      val owner      =
        if (hostClass == null) internalName(field.owner)
        else                  internalName(hostClass)
      val fieldJName = field.javaSimpleName.toString
      val fieldDescr = symInfoTK(field).getDescriptor
      val isStatic   = field.isStaticMember
      val opc =
        if (isLoad) { if (isStatic) asm.Opcodes.GETSTATIC else asm.Opcodes.GETFIELD }
        else       { if (isStatic) asm.Opcodes.PUTSTATIC else asm.Opcodes.PUTFIELD }
      mnode.visitFieldInsn(opc, owner, fieldJName, fieldDescr)

    }

    // ---------------- emitting constant values ----------------

    /*
     * For const.tag in {ClazzTag, EnumTag}
     *   must-single-thread
     * Otherwise it's safe to call from multiple threads.
     */
    def genConstant(const: Constant) {
      (const.tag: @switch) match {

        case BooleanTag => bc.boolconst(const.booleanValue)

        case ByteTag    => bc.iconst(const.byteValue)
        case ShortTag   => bc.iconst(const.shortValue)
        case CharTag    => bc.iconst(const.charValue)
        case IntTag     => bc.iconst(const.intValue)

        case LongTag    => bc.lconst(const.longValue)
        case FloatTag   => bc.fconst(const.floatValue)
        case DoubleTag  => bc.dconst(const.doubleValue)

        case UnitTag    => ()

        case StringTag  =>
          assert(const.value != null, const) // TODO this invariant isn't documented in `case class Constant`
          mnode.visitLdcInsn(const.stringValue) // `stringValue` special-cases null, but not for a const with StringTag

        case NullTag    => emit(asm.Opcodes.ACONST_NULL)

        case ClazzTag   =>
          val toPush: BType = {
            val kind = toTypeKind(const.typeValue)
            if (kind.isValueType) classLiteral(kind)
            else kind;
          }
          mnode.visitLdcInsn(toPush.toASMType)

        case EnumTag   =>
          val sym       = const.symbolValue
          val ownerName = internalName(sym.owner)
          val fieldName = sym.javaSimpleName.toString
          val fieldDesc = toTypeKind(sym.tpe.underlying).getDescriptor
          mnode.visitFieldInsn(
            asm.Opcodes.GETSTATIC,
            ownerName,
            fieldName,
            fieldDesc
          )

        case _ => abort("Unknown constant value: " + const)
      }
    }

    private def genLabelDef(lblDf: LabelDef, expectedType: BType) {
      // duplication of LabelDefs contained in `finally`-clauses is handled when emitting RETURN. No bookkeeping for that required here.
      // no need to call index() over lblDf.params, on first access that magic happens (moreover, no LocalVariableTable entries needed for them).
      markProgramPoint(programPoint(lblDf.symbol))
      lineNumber(lblDf)
      genLoad(lblDf.rhs, expectedType)
    }

    private def genReturn(r: Return) {
      val Return(expr) = r
      val returnedKind = tpeTK(expr)
      genLoad(expr, returnedKind)
      adapt(returnedKind, returnType)
      val saveReturnValue = (returnType != UNIT)
      lineNumber(r)

      cleanups match {
        case Nil =>
          // not an assertion: !shouldEmitCleanup (at least not yet, pendingCleanups() may still have to run, and reset `shouldEmitCleanup`.
          bc emitRETURN returnType
        case nextCleanup :: rest =>
          if (saveReturnValue) {
            if (insideCleanupBlock) {
              cunit.warning(r.pos, "Return statement found in finally-clause, discarding its return-value in favor of that of a more deeply nested return.")
              bc drop returnType
            } else {
              // regarding return value, the protocol is: in place of a `return-stmt`, a sequence of `adapt, store, jump` are inserted.
              if (earlyReturnVar == null) {
                earlyReturnVar = makeLocal(returnType, "earlyReturnVar")
              }
              store(earlyReturnVar)
            }
          }
          bc goTo nextCleanup
          shouldEmitCleanup = true
      }

    } // end of genReturn()

    private def genApply(app: Apply, expectedType: BType): BType = {
      var generatedType = expectedType
      lineNumber(app)
      app match {

        case Apply(TypeApply(fun, targs), _) =>

          val sym = fun.symbol
          val cast = sym match {
            case Object_isInstanceOf  => false
            case Object_asInstanceOf  => true
            case _                    => abort("Unexpected type application " + fun + "[sym: " + sym.fullName + "]" + " in: " + app)
          }

          val Select(obj, _) = fun
          val l = tpeTK(obj)
          val r = tpeTK(targs.head)

              def genTypeApply(): BType = {
                genLoadQualifier(fun)

                if (l.isValueType && r.isValueType)
                  genConversion(l, r, cast)
                else if (l.isValueType) {
                  bc drop l
                  if (cast) {
                    mnode.visitTypeInsn(asm.Opcodes.NEW, classCastExceptionReference.getInternalName)
                    bc dup ObjectReference
                    emit(asm.Opcodes.ATHROW)
                  } else {
                    bc boolconst false
                  }
                }
                else if (r.isValueType && cast) {
                  abort("Erasure should have added an unboxing operation to prevent this cast. Tree: " + app)
                }
                else if (r.isValueType) {
                  bc isInstance classLiteral(r)
                }
                else {
                  genCast(r, cast)
                }

                if (cast) r else BOOL
              } // end of genTypeApply()

          generatedType = genTypeApply()

        // 'super' call: Note: since constructors are supposed to
        // return an instance of what they construct, we have to take
        // special care. On JVM they are 'void', and Scala forbids (syntactically)
        // to call super constructors explicitly and/or use their 'returned' value.
        // therefore, we can ignore this fact, and generate code that leaves nothing
        // on the stack (contrary to what the type in the AST says).
        case Apply(fun @ Select(Super(_, mix), _), args) =>
          val invokeStyle = icodes.opcodes.SuperCall(mix)
          // if (fun.symbol.isConstructor) Static(true) else SuperCall(mix);
          mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
          genLoadArguments(args, paramTKs(app))
          genCallMethod(fun.symbol, invokeStyle, pos = app.pos)
          generatedType = asmMethodType(fun.symbol).getReturnType

        // 'new' constructor call: Note: since constructors are
        // thought to return an instance of what they construct,
        // we have to 'simulate' it by DUPlicating the freshly created
        // instance (on JVM, <init> methods return VOID).
        case Apply(fun @ Select(New(tpt), nme.CONSTRUCTOR), args) =>
          val ctor = fun.symbol
          assert(ctor.isClassConstructor, "'new' call to non-constructor: " + ctor.name)

          generatedType = tpeTK(tpt)
          assert(generatedType.isRefOrArrayType, "Non reference type cannot be instantiated: " + generatedType)

          generatedType match {
            case arr if generatedType.isArray =>
              genLoadArguments(args, paramTKs(app))
              val dims     = arr.getDimensions
              var elemKind = arr.getElementType
              val argsSize = args.length
              if (argsSize > dims) {
                cunit.error(app.pos, "too many arguments for array constructor: found " + args.length +
                                      " but array has only " + dims + " dimension(s)")
              }
              if (argsSize < dims) {
                /* In one step:
                 *   elemKind = new BType(BType.ARRAY, arr.off + argsSize, arr.len - argsSize)
                 * however the above does not enter a TypeName for each nested arrays in chrs.
                 */
                for (i <- args.length until dims) elemKind = arrayOf(elemKind)
              }
              (argsSize : @switch) match {
                case 1 => bc newarray elemKind
                case _ =>
                  val descr = ('[' * argsSize) + elemKind.getDescriptor // denotes the same as: arrayN(elemKind, argsSize).getDescriptor
                  mnode.visitMultiANewArrayInsn(descr, argsSize)
              }

            case rt if generatedType.hasObjectSort =>
              assert(exemplar(ctor.owner).c == rt, "Symbol " + ctor.owner.fullName + " is different from " + rt)
              mnode.visitTypeInsn(asm.Opcodes.NEW, rt.getInternalName)
              bc dup generatedType
              genLoadArguments(args, paramTKs(app))
              genCallMethod(ctor, icodes.opcodes.Static(onInstance = true))

            case _ =>
              abort("Cannot instantiate " + tpt + " of kind: " + generatedType)
          }

        case Apply(fun @ _, List(expr)) if (definitions.isBox(fun.symbol)) =>
          val nativeKind = tpeTK(expr)
          genLoad(expr, nativeKind)
          val MethodNameAndType(mname, mdesc) = asmBoxTo(nativeKind)
          bc.invokestatic(BoxesRunTime.getInternalName, mname, mdesc)
          generatedType = boxResultType(fun.symbol) // was toTypeKind(fun.symbol.tpe.resultType)

        case Apply(fun @ _, List(expr)) if (definitions.isUnbox(fun.symbol)) =>
          genLoad(expr, tpeTK(expr))
          val boxType = unboxResultType(fun.symbol) // was toTypeKind(fun.symbol.owner.linkedClassOfClass.tpe)
          generatedType = boxType
          val MethodNameAndType(mname, mdesc) = asmUnboxTo(boxType)
          bc.invokestatic(BoxesRunTime.getInternalName, mname, mdesc)

        case app @ Apply(fun, args) =>
          val sym = fun.symbol

          if (sym.isLabel) {  // jump to a label
            genLoadLabelArguments(args, labelDef(sym), app.pos)
            bc goTo programPoint(sym)
          } else if (isPrimitive(sym)) { // primitive method call
            generatedType = genPrimitiveOp(app, expectedType)
          } else {  // normal method call

                def genNormalMethodCall() {

                  val invokeStyle =
                    if (sym.isStaticMember) icodes.opcodes.Static(onInstance = false)
                    else if (sym.isPrivate || sym.isClassConstructor) icodes.opcodes.Static(onInstance = true)
                    else icodes.opcodes.Dynamic;

                  if (invokeStyle.hasInstance) {
                    genLoadQualifier(fun)
                  }

                  genLoadArguments(args, paramTKs(app))

                  // In "a couple cases", squirrel away a extra information (hostClass, targetTypeKind). TODO Document what "in a couple cases" refers to.
                  var hostClass:      Symbol = null
                  var targetTypeKind: BType  = null
                  fun match {
                    case Select(qual, _) =>
                      val qualSym = findHostClass(qual.tpe, sym)
                      if (qualSym == ArrayClass) {
                        targetTypeKind = tpeTK(qual)
                        log(s"Stored target type kind for {$sym.fullName} as $targetTypeKind")
                      }
                      else {
                        hostClass = qualSym
                        if (qual.tpe.typeSymbol != qualSym) {
                          log(s"Precisified host class for $sym from ${qual.tpe.typeSymbol.fullName} to ${qualSym.fullName}")
                        }
                      }

                    case _ =>
                  }
                  if ((targetTypeKind != null) && (sym == definitions.Array_clone) && invokeStyle.isDynamic) {
                    val target: String = targetTypeKind.getInternalName
                    bc.invokevirtual(target, "clone", "()Ljava/lang/Object;")
                  }
                  else {
                    genCallMethod(sym, invokeStyle, hostClass, app.pos)
                  }

                } // end of genNormalMethodCall()

            genNormalMethodCall()

            generatedType = asmMethodType(sym).getReturnType
      }

      }

      generatedType
    } // end of PlainClassBuilder's genApply()

    private def genArrayValue(av: ArrayValue): BType = {
      val ArrayValue(tpt @ TypeTree(), elems) = av

      val elmKind       = tpeTK(tpt)
      val generatedType = arrayOf(elmKind)

      lineNumber(av)
      bc iconst   elems.length
      bc newarray elmKind

      var i = 0
      var rest = elems
      while (!rest.isEmpty) {
        bc dup     generatedType
        bc iconst  i
        genLoad(rest.head, elmKind)
        bc astore  elmKind
        rest = rest.tail
        i = i + 1
      }

      generatedType
    }

    /*
     * A Match node contains one or more case clauses,
     * each case clause lists one or more Int values to use as keys, and a code block.
     * Except the "default" case clause which (if it exists) doesn't list any Int key.
     *
     * On a first pass over the case clauses, we flatten the keys and their targets (the latter represented with asm.Labels).
     * That representation allows JCodeMethodV to emit a lookupswitch or a tableswitch.
     *
     * On a second pass, we emit the switch blocks, one for each different target.
     */
    private def genMatch(tree: Match): BType = {
      lineNumber(tree)
      genLoad(tree.selector, INT)
      val generatedType = tpeTK(tree)

      var flatKeys: List[Int]       = Nil
      var targets:  List[asm.Label] = Nil
      var default:  asm.Label       = null
      var switchBlocks: List[Pair[asm.Label, Tree]] = Nil

      // collect switch blocks and their keys, but don't emit yet any switch-block.
      for (caze @ CaseDef(pat, guard, body) <- tree.cases) {
        assert(guard == EmptyTree, guard)
        val switchBlockPoint = new asm.Label
        switchBlocks ::= Pair(switchBlockPoint, body)
        pat match {
          case Literal(value) =>
            flatKeys ::= value.intValue
            targets  ::= switchBlockPoint
          case Ident(nme.WILDCARD) =>
            assert(default == null, "multiple default targets in a Match node, at " + tree.pos)
            default = switchBlockPoint
          case Alternative(alts) =>
            alts foreach {
              case Literal(value) =>
                flatKeys ::= value.intValue
                targets  ::= switchBlockPoint
              case _ =>
                abort("Invalid alternative in alternative pattern in Match node: " + tree + " at: " + tree.pos)
            }
          case _ =>
            abort("Invalid pattern in Match node: " + tree + " at: " + tree.pos)
        }
      }
      bc.emitSWITCH(mkArrayReverse(flatKeys), mkArray(targets.reverse), default, MIN_SWITCH_DENSITY)

      // emit switch-blocks.
      val postMatch = new asm.Label
      for (sb <- switchBlocks.reverse) {
        val Pair(caseLabel, caseBody) = sb
        markProgramPoint(caseLabel)
        genLoad(caseBody, generatedType)
        bc goTo postMatch
      }

      markProgramPoint(postMatch)
      generatedType
    }

    def genBlock(tree: Block, expectedType: BType) {
      val Block(stats, expr) = tree
      val savedScope = varsInScope
      varsInScope = Nil
      stats foreach genStat
      genLoad(expr, expectedType)
      val end = currProgramPoint()
      if (emitVars) { // add entries to LocalVariableTable JVM attribute
        for (Pair(sym, start) <- varsInScope.reverse) { emitLocalVarScope(sym, start, end) }
      }
      varsInScope = savedScope
    }

    def adapt(from: BType, to: BType) {
      if (!conforms(from, to)) {
        to match {
          case UNIT => bc drop from
          case _    => bc.emitT2T(from, to)
        }
      } else if (from.isNothingType) {
        emit(asm.Opcodes.ATHROW) // ICode enters here into enterIgnoreMode, we'll rely instead on DCE at ClassNode level.
      } else if (from.isNullType) {
        bc drop from
        mnode.visitInsn(asm.Opcodes.ACONST_NULL)
      }
      else (from, to) match  {
        case (BYTE, LONG) | (SHORT, LONG) | (CHAR, LONG) | (INT, LONG) => bc.emitT2T(INT, LONG)
        case _ => ()
      }
    }

    /* Emit code to Load the qualifier of `tree` on top of the stack. */
    def genLoadQualifier(tree: Tree) {
      lineNumber(tree)
      tree match {
        case Select(qualifier, _) => genLoad(qualifier, tpeTK(qualifier))
        case _                    => abort("Unknown qualifier " + tree)
      }
    }

    /* Generate code that loads args into label parameters. */
    def genLoadLabelArguments(args: List[Tree], lblDef: LabelDef, gotoPos: Position) {
      assert(args forall { a => !a.hasSymbolField || a.hasSymbolWhich( s => !s.isLabel) }, "SI-6089 at: " + gotoPos) // SI-6089

      val aps = {
        val params: List[Symbol] = lblDef.params.map(_.symbol)
        assert(args.length == params.length, "Wrong number of arguments in call to label at: " + gotoPos)

            def isTrivial(kv: (Tree, Symbol)) = kv match {
              case (This(_), p) if p.name == nme.THIS     => true
              case (arg @ Ident(_), p) if arg.symbol == p => true
              case _                                      => false
            }

        (args zip params) filterNot isTrivial
      }

      // first push *all* arguments. This makes sure muliple uses of the same labelDef-var will all denote the (previous) value.
      aps foreach { case (arg, param) => genLoad(arg, locals(param).tk) } // `locals` is known to contain `param` because `genDefDef()` visited `labelDefsAtOrUnder`

      // second assign one by one to the LabelDef's variables.
      aps.reverse foreach {
        case (_, param) =>
          // TODO FIXME a "this" param results from tail-call xform. If so, the `else` branch seems perfectly fine. And the `then` branch must be wrong.
          if (param.name == nme.THIS) mnode.visitVarInsn(asm.Opcodes.ASTORE, 0)
          else store(param)
      }

    }

    def genLoadArguments(args: List[Tree], btpes: List[BType]) {
      (args zip btpes) foreach { case (arg, btpe) => genLoad(arg, btpe) }
    }

    def genLoadModule(tree: Tree): BType = {
      // Working around SI-5604.  Rather than failing the compile when we see a package here, check if there's a package object.
      val module = (
        if (!tree.symbol.isPackageClass) tree.symbol
        else tree.symbol.info.member(nme.PACKAGE) match {
          case NoSymbol => abort("Cannot use package as value: " + tree) ; NoSymbol
          case s        => devWarning("Bug: found package class where package object expected.  Converting.") ; s.moduleClass
        }
      )
      lineNumber(tree)
      genLoadModule(module)
      asmClassType(module)
    }

    def genLoadModule(module: Symbol) {
      if (claszSymbol == module.moduleClass && jMethodName != "readResolve") {
        mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
      } else {
        val mbt  = asmClassType(module)
        mnode.visitFieldInsn(
          asm.Opcodes.GETSTATIC,
          mbt.getInternalName /* + "$" */ ,
          strMODULE_INSTANCE_FIELD,
          mbt.getDescriptor // for nostalgics: toTypeKind(module.tpe).getDescriptor
        )
      }
    }

    def genConversion(from: BType, to: BType, cast: Boolean) = {
      if (cast) { bc.emitT2T(from, to) }
      else {
        bc drop from
        bc boolconst (from == to)
      }
    }

    def genCast(to: BType, cast: Boolean) {
      if (cast) { bc checkCast  to }
      else      { bc isInstance to }
    }

    /* Is the given symbol a primitive operation? */
    def isPrimitive(fun: Symbol): Boolean = scalaPrimitives.isPrimitive(fun)

    /* Generate coercion denoted by "code" */
    def genCoercion(code: Int) = {
      import scalaPrimitives._
      (code: @switch) match {
        case B2B | S2S | C2C | I2I | L2L | F2F | D2D => ()
        case _ =>
          val from = coercionFrom(code)
          val to   = coercionTo(code)
          bc.emitT2T(from, to)
      }
    }

    def genStringConcat(tree: Tree): BType = {
      lineNumber(tree)
      liftStringConcat(tree) match {

        // Optimization for expressions of the form "" + x.  We can avoid the StringBuilder.
        case List(Literal(Constant("")), arg) =>
          genLoad(arg, ObjectReference)
          genCallMethod(String_valueOf, icodes.opcodes.Static(false))

        case concatenations =>
          bc.genStartConcat
          for (elem <- concatenations) {
            val kind = tpeTK(elem)
            genLoad(elem, kind)
            bc.genStringConcat(kind)
          }
          bc.genEndConcat

      }

      StringReference
    }

    def genCallMethod(method: Symbol, style: InvokeStyle, hostClass0: Symbol = null, pos: Position = NoPosition) {

      val siteSymbol = claszSymbol
      val hostSymbol = if (hostClass0 == null) method.owner else hostClass0;
      val methodOwner = method.owner
      // info calls so that types are up to date; erasure may add lateINTERFACE to traits
      hostSymbol.info ; methodOwner.info

          def needsInterfaceCall(sym: Symbol) = (
               sym.isInterface
            || sym.isJavaDefined && sym.isNonBottomSubClass(definitions.ClassfileAnnotationClass)
          )

          def isAccessibleFrom(target: Symbol, site: Symbol): Boolean = {
            target.isPublic || target.isProtected && {
              (site.enclClass isSubClass target.enclClass) ||
              (site.enclosingPackage == target.privateWithin)
            }
          }

      // whether to reference the type of the receiver or
      // the type of the method owner
      val useMethodOwner = (
           style != icodes.opcodes.Dynamic
        || hostSymbol.isBottomClass
        || methodOwner == definitions.ObjectClass
      )
      val receiver = if (useMethodOwner) methodOwner else hostSymbol
      val bmOwner  = asmClassType(receiver)
      val jowner   = bmOwner.getInternalName
      val jname    = method.javaSimpleName.toString
      val bmType   = asmMethodType(method)
      val mdescr   = bmType.getDescriptor

          def initModule() {
            // we initialize the MODULE$ field immediately after the super ctor
            if (!isModuleInitialized &&
                jMethodName == INSTANCE_CONSTRUCTOR_NAME &&
                jname == INSTANCE_CONSTRUCTOR_NAME &&
                isStaticModule(siteSymbol)) {
              isModuleInitialized = true
              mnode.visitVarInsn(asm.Opcodes.ALOAD, 0)
              mnode.visitFieldInsn(
                asm.Opcodes.PUTSTATIC,
                thisName,
                strMODULE_INSTANCE_FIELD,
                "L" + thisName + ";"
              )
            }
          }

      if (style.isStatic) {
        if (style.hasInstance) { bc.invokespecial  (jowner, jname, mdescr) }
        else                   { bc.invokestatic   (jowner, jname, mdescr) }
      }
      else if (style.isDynamic) {
        if (needsInterfaceCall(receiver)) { bc.invokeinterface(jowner, jname, mdescr) }
        else                              { bc.invokevirtual  (jowner, jname, mdescr) }
      }
      else {
        assert(style.isSuper, "An unknown InvokeStyle: " + style)
        bc.invokespecial(jowner, jname, mdescr)
        initModule()
      }

    } // end of genCallMethod()

    /* Generate the scala ## method. */
    def genScalaHash(tree: Tree): BType = {
      genLoadModule(ScalaRunTimeModule) // TODO why load ScalaRunTimeModule if ## has InvokeStyle of Static(false) ?
      genLoad(tree, ObjectReference)
      genCallMethod(hashMethodSym, icodes.opcodes.Static(onInstance = false))

      INT
    }

    /*
     * Returns a list of trees that each should be concatenated, from left to right.
     * It turns a chained call like "a".+("b").+("c") into a list of arguments.
     */
    def liftStringConcat(tree: Tree): List[Tree] = tree match {
      case Apply(fun @ Select(larg, method), rarg) =>
        if (isPrimitive(fun.symbol) &&
            scalaPrimitives.getPrimitive(fun.symbol) == scalaPrimitives.CONCAT)
          liftStringConcat(larg) ::: rarg
        else
          tree :: Nil
      case _ =>
        tree :: Nil
    }

    /* Some useful equality helpers. */
    def isNull(t: Tree) = {
      t match {
        case Literal(Constant(null)) => true
        case _ => false
      }
    }

    /* If l or r is constant null, returns the other ; otherwise null */
    def ifOneIsNull(l: Tree, r: Tree) = if (isNull(l)) r else if (isNull(r)) l else null

    /* Emit code to compare the two top-most stack values using the 'op' operator. */
    private def genCJUMP(success: asm.Label, failure: asm.Label, op: TestOp, tk: BType) {
      if (tk.isIntSizedType) { // BOOL, BYTE, CHAR, SHORT, or INT
        bc.emitIF_ICMP(op, success)
      } else if (tk.isRefOrArrayType) { // REFERENCE(_) | ARRAY(_)
        bc.emitIF_ACMP(op, success)
      } else {
        (tk: @unchecked) match {
          case LONG   => emit(asm.Opcodes.LCMP)
          case FLOAT  =>
            if (op == icodes.LT || op == icodes.LE) emit(asm.Opcodes.FCMPG)
            else emit(asm.Opcodes.FCMPL)
          case DOUBLE =>
            if (op == icodes.LT || op == icodes.LE) emit(asm.Opcodes.DCMPG)
            else emit(asm.Opcodes.DCMPL)
        }
        bc.emitIF(op, success)
      }
      bc goTo failure
    }

    /* Emits code to compare (and consume) stack-top and zero using the 'op' operator */
    private def genCZJUMP(success: asm.Label, failure: asm.Label, op: TestOp, tk: BType) {
      if (tk.isIntSizedType) { // BOOL, BYTE, CHAR, SHORT, or INT
        bc.emitIF(op, success)
      } else if (tk.isRefOrArrayType) { // REFERENCE(_) | ARRAY(_)
        // @unchecked because references aren't compared with GT, GE, LT, LE.
        (op : @unchecked) match {
          case icodes.EQ => bc emitIFNULL    success
          case icodes.NE => bc emitIFNONNULL success
        }
      } else {
        (tk: @unchecked) match {
          case LONG   =>
            emit(asm.Opcodes.LCONST_0)
            emit(asm.Opcodes.LCMP)
          case FLOAT  =>
            emit(asm.Opcodes.FCONST_0)
            if (op == icodes.LT || op == icodes.LE) emit(asm.Opcodes.FCMPG)
            else emit(asm.Opcodes.FCMPL)
          case DOUBLE =>
            emit(asm.Opcodes.DCONST_0)
            if (op == icodes.LT || op == icodes.LE) emit(asm.Opcodes.DCMPG)
            else emit(asm.Opcodes.DCMPL)
        }
        bc.emitIF(op, success)
      }
      bc goTo failure
    }

    val testOpForPrimitive: Array[TestOp] = Array(
      icodes.EQ, icodes.NE, icodes.EQ, icodes.NE, icodes.LT, icodes.LE, icodes.GE, icodes.GT
    )

    /*
     * Generate code for conditional expressions.
     * The jump targets success/failure of the test are `then-target` and `else-target` resp.
     */
    private def genCond(tree: Tree, success: asm.Label, failure: asm.Label) {

          def genComparisonOp(l: Tree, r: Tree, code: Int) {
            val op: TestOp = testOpForPrimitive(code - scalaPrimitives.ID)
            // special-case reference (in)equality test for null (null eq x, x eq null)
            var nonNullSide: Tree = null
            if (scalaPrimitives.isReferenceEqualityOp(code) &&
                { nonNullSide = ifOneIsNull(l, r); nonNullSide != null }
            ) {
              genLoad(nonNullSide, ObjectReference)
              genCZJUMP(success, failure, op, ObjectReference)
            }
            else {
              val tk = maxType(tpeTK(l), tpeTK(r))
              genLoad(l, tk)
              genLoad(r, tk)
              genCJUMP(success, failure, op, tk)
            }
          }

          def default() = {
            genLoad(tree, BOOL)
            genCZJUMP(success, failure, icodes.NE, BOOL)
          }

      lineNumber(tree)
      tree match {

        case Apply(fun, args) if isPrimitive(fun.symbol) =>
          import scalaPrimitives.{ ZNOT, ZAND, ZOR, EQ, getPrimitive }

          // lhs and rhs of test
          lazy val Select(lhs, _) = fun
          val rhs = if (args.isEmpty) EmptyTree else args.head; // args.isEmpty only for ZNOT

              def genZandOrZor(and: Boolean) = { // TODO WRONG
                // reaching "keepGoing" indicates the rhs should be evaluated too (ie not short-circuited).
                val keepGoing = new asm.Label

                if (and) genCond(lhs, keepGoing, failure)
                else     genCond(lhs, success,   keepGoing)

                markProgramPoint(keepGoing)
                genCond(rhs, success, failure)
              }

          getPrimitive(fun.symbol) match {
            case ZNOT   => genCond(lhs, failure, success)
            case ZAND   => genZandOrZor(and = true)
            case ZOR    => genZandOrZor(and = false)
            case code   =>
              // TODO !!!!!!!!!! isReferenceType, in the sense of TypeKind? (ie non-array, non-boxed, non-nothing, may be null)
              if (scalaPrimitives.isUniversalEqualityOp(code) && tpeTK(lhs).hasObjectSort) {
                // `lhs` has reference type
                if (code == EQ) genEqEqPrimitive(lhs, rhs, success, failure)
                else            genEqEqPrimitive(lhs, rhs, failure, success)
              }
              else if (scalaPrimitives.isComparisonOp(code))
                genComparisonOp(lhs, rhs, code)
              else
                default
          }

        case _ => default
      }

    } // end of genCond()

    /*
     * Generate the "==" code for object references. It is equivalent of
     * if (l eq null) r eq null else l.equals(r);
     *
     * @param l       left-hand-side  of the '=='
     * @param r       right-hand-side of the '=='
     */
    def genEqEqPrimitive(l: Tree, r: Tree, success: asm.Label, failure: asm.Label) {

      /* True if the equality comparison is between values that require the use of the rich equality
       * comparator (scala.runtime.Comparator.equals). This is the case when either side of the
       * comparison might have a run-time type subtype of java.lang.Number or java.lang.Character.
       * When it is statically known that both sides are equal and subtypes of Number of Character,
       * not using the rich equality is possible (their own equals method will do ok.)
       */
      val mustUseAnyComparator: Boolean = {
        val areSameFinals = l.tpe.isFinalType && r.tpe.isFinalType && (l.tpe =:= r.tpe)

        !areSameFinals && platform.isMaybeBoxed(l.tpe.typeSymbol) && platform.isMaybeBoxed(r.tpe.typeSymbol)
      }

      if (mustUseAnyComparator) {
        val equalsMethod = {
            def default = platform.externalEquals
            platform match {
              case x: JavaPlatform =>
                import x._
                  if (l.tpe <:< BoxedNumberClass.tpe) {
                    if (r.tpe <:< BoxedNumberClass.tpe) externalEqualsNumNum
                    else if (r.tpe <:< BoxedCharacterClass.tpe) externalEqualsNumChar
                    else externalEqualsNumObject
                  }
                  else default

              case _ => default
            }
          }
        genLoad(l, ObjectReference)
        genLoad(r, ObjectReference)
        genCallMethod(equalsMethod, icodes.opcodes.Static(onInstance = false))
        genCZJUMP(success, failure, icodes.NE, BOOL)
      }
      else {
        if (isNull(l)) {
          // null == expr -> expr eq null
          genLoad(r, ObjectReference)
          genCZJUMP(success, failure, icodes.EQ, ObjectReference)
        } else if (isNull(r)) {
          // expr == null -> expr eq null
          genLoad(l, ObjectReference)
          genCZJUMP(success, failure, icodes.EQ, ObjectReference)
        } else {
          // l == r -> if (l eq null) r eq null else l.equals(r)
          val eqEqTempLocal = makeLocal(AnyRefReference, nme.EQEQ_LOCAL_VAR.toString)
          val lNull    = new asm.Label
          val lNonNull = new asm.Label

          genLoad(l, ObjectReference)
          genLoad(r, ObjectReference)
          store(eqEqTempLocal)
          bc dup ObjectReference
          genCZJUMP(lNull, lNonNull, icodes.EQ, ObjectReference)

          markProgramPoint(lNull)
          bc drop ObjectReference
          load(eqEqTempLocal)
          genCZJUMP(success, failure, icodes.EQ, ObjectReference)

          markProgramPoint(lNonNull)
          load(eqEqTempLocal)
          genCallMethod(Object_equals, icodes.opcodes.Dynamic)
          genCZJUMP(success, failure, icodes.NE, BOOL)
        }
      }
    }

    /* Does this tree have a try-catch block? */
    def mayCleanStack(tree: Tree): Boolean = tree exists { t => t.isInstanceOf[Try] }

    /* can-multi-thread */
    def getMaxType(ts: List[Type]): BType = {
      ts map toTypeKind reduceLeft maxType
    }

    abstract class Cleanup(val value: AnyRef) {
      def contains(x: AnyRef) = value == x
    }
    case class MonitorRelease(v: Symbol) extends Cleanup(v) { }
    case class Finalizer(f: Tree) extends Cleanup (f) { }

    trait EHClause
    case class NamelessEH(typeToDrop: BType,  caseBody: Tree) extends EHClause
    case class BoundEH    (patSymbol: Symbol, caseBody: Tree) extends EHClause

  } // end of class PlainClassBuilder

}
