/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala
package tools.nsc
package backend
package jvm

import scala.collection.{ mutable, immutable }

import scala.tools.asm

/*
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeLateClosuBuilder extends BCodeSkelBuilder {
  import global._
  import asm.tree.{MethodNode, FieldNode}

  /*
   *  Besides emitting a Late-Closure-Class, `genLateClosure()` collects information
   *  about the endpoint targeted by that dclosure as a `DClosureEndpoint` instance.
   *  That way, once `PlainClassBuilder.genPlainClass()` has built an ASM ClassNode,
   *  the ASM MethodNodes for the endpoints can be added to the `BCodeOptInter.closuRepo.endpoint` map.
   *
   *  @param epName    name of the endpoint method
   *  @param epMT      ASM method type of the endpoint
   *  @param closuBT   BType of the dclosure-class targeting the endpoint
   *  @param closuCtor the only constructor of the dclosure
   *
   */
  case class DClosureEndpoint(epName: String, epMT: BType, closuBT: BType, closuCtor: MethodNode)

  abstract class LateClosureBuilder(cunit: CompilationUnit) extends PlainSkelBuilder(cunit) {

    var lateClosures: List[asm.tree.ClassNode] = Nil

    /*
     *  Allows detecting which LCCs have been already emitted (a "second" instantiation of "the same"
     *  anon-closure-class is possible, in the instructions resulting from duplicating a finalizer).
     */
    val closuresForDelegates = mutable.Map.empty[MethodSymbol, DClosureEndpoint]

    def fakeCallsiteExtractor(fakeCallsiteWrapper: Tree): Apply = {

      val ft = new FindTreeTraverser( {
        case app: Apply => app.symbol.name.startsWith("dlgt") // if you think about it, this un-equivocally picks the correct tree.
        case _          => false
      } )
      ft.traverse(fakeCallsiteWrapper)
      val fakeApp = ft.result.get

      fakeApp.asInstanceOf[Apply]
    }

    /*
     *  This method works in tandem with UnCurry's closureConversionModern()
     *
     *  Rather than emitting a fakeCallsite, the initialization of a closure instance is emitted, along with
     *  a closure class that is synthesized on the spot (a so called "delegating closure" or dclosure for short).
     *  The result is undistinguishable from what UnCurry, Specialization, Erasure, would have produced.
     *
     *  Terminology: arity is used throughout `genLateClosure()` as shorthand for closure-arity
     *
     *  The starting point is the "fake calliste" targeting the closure entrypoint (aka "delegate").
     *
     *    (a) The "fake calliste" may target:
     *          - a static method (e.g., for closures enclosed in implementation classes);
     *        or
     *          - an instance method (the receiver being the outer instance of the dclosure).
     *            An anon-closure enclosed in a static module also has an instance method as endpoint,
     *            however the apply() we'll emit will grab that instance via MODULE$ as opposed to capturing an outer value.
     *
     *    (b) Whenever the delegate is an instance method,
     *        the leading `arity` arguments to the fakeCallsite are Trees denoting zeroes.
     *        The above also applies in case of a static delegate unless declared in an implementation class.
     *        In that case:
     *          - the first argument stands for the self-instance, which should be captured by the dclosure.
     *          - the following `arity` arguments are zeroes.
     *
     *    (c) remaining arguments denote non-outer captured values.
     *        Whether an outer-instance is needed is determined by
     *          (c.1) whether the delegate will be invoked via invokevirtual or invokestatic,
     *                in turn determined by `delegateSym.isStaticMember`
     *          (c.2) whether the delegate is owned by a static module,
     *                no $outer field is needed in this case.
     *
     *  The resulting Late-Closure-Class is registered in `codeRepo.classes` and `exemplars`
     *  by `PlainClassBuilder.genPlainClass()` , see `PlainClassBuilder.lateClosures`
     *
     *  The resulting Late-Closure-Class consists of:
     *
     *    (d) one public constructor taking as argument the outer value (if needed) followed by (c).
     *    (e) a private final field for each constructor param
     *    (f) one, two, or three "apply()" overrides to account for specialization.
     *
     *  @return the closure-type, ie the 2nd argument (`castToBT`)
     *
     */
    def genLateClosure(fakeCallsite: Apply, castToBT: BType): BType = {
      val Apply(Select(rcv, _), args) = fakeCallsite
      val arity = abstractFunctionArity(castToBT)

      val delegateSym = fakeCallsite.symbol.asInstanceOf[MethodSymbol]
      val hasStaticModuleOwner = isStaticModule(delegateSym.owner)
      val hasOuter = !delegateSym.isStaticMember && !hasStaticModuleOwner
      val isImplClassEndpoint = delegateSym.owner.isImplClass

      assert(
        if (isImplClassEndpoint) !hasOuter else true,
         "How come a delegate-method (for a Late-Closure-Class) is static yet the dclosure is supposed to have an outer-instance. " +
        s"Delegate: ${delegateSym.fullLocationString}"
      )
      assert(
        if (hasOuter) !isImplClassEndpoint else true,
         "A Late-Closure-Class that captures an outer-instance can't delegate to a (static) method in an implementation class. " +
        s"Delegate: ${delegateSym.fullLocationString}"
      )

      // checking working assumptions

      // outerTK is a poor name choice because sometimes there's no outer instance yet there's always a delegateOwnerTK
      val outerTK     = brefType(internalName(delegateSym.owner))
      val enclClassBT = brefType(cnode.name)
      assert(outerTK.hasObjectSort, s"Not of object sort: $outerTK")
      assert(
        outerTK == enclClassBT,
         "Probable cause: a regression in the way DelayedInit is lowered. " +
        s"outerTK != enclClassBT , where outerTK is $outerTK and enclClassBT is $enclClassBT"
      )

      /*
       * Pieces of information for building the closure class:
       *   - closure-state (names and types),
       *   - apply-params-section (types).
       */

      val delegateMT: BType = asmMethodType(delegateSym)
      val delegateJavaName  = delegateSym.javaSimpleName.toString

      val delegateParamTs = delegateMT.getArgumentTypes.toList
      val closuStateBTs: List[BType] = {
        if (isImplClassEndpoint) {
          delegateParamTs.head :: delegateParamTs.tail.drop(arity)
        }
        else {
          val tmp = delegateParamTs.drop(arity)
          if (hasOuter) outerTK :: tmp else tmp
        }
      }

      val closuStateNames: List[String] = {
        val delegateParamNames: List[String] = uniquify(
          for(paramSym <- delegateSym.paramss.head) yield paramSym.name.toString
        )
        ifDebug {
          assert(allDifferent(delegateParamNames), "Duplicate param names found among " + delegateParamNames.mkString(" , "))
        }
        if (isImplClassEndpoint) {
          delegateParamNames.head :: delegateParamNames.tail.drop(arity)
        }
        else {
          val tmp = delegateParamNames.drop(arity)
          if (hasOuter) nme.OUTER.toString :: tmp else tmp
        }
      }

      val delegateApplySection: List[BType] = {
        if (isImplClassEndpoint) { delegateParamTs.tail.take(arity) }
        else { delegateParamTs.take(arity) }
      }

      def emitClosureInstantiation(closuInternalName: String, ctorDescr: String) {
        assert(closuInternalName != null)
        assert(ctorDescr != null)
        // NEW, DUP
        mnode.visitTypeInsn(asm.Opcodes.NEW, closuInternalName)
        mnode.visitInsn(asm.Opcodes.DUP)
        // outer value, if any
        val restClosureStateBTs: List[BType] =
          if (hasOuter) {
            genLoad(rcv, outerTK)
            closuStateBTs.drop(1)
          } else {
            closuStateBTs
          }
        // the rest of captured values
        val capturedValues: List[Tree] = {
          if (isImplClassEndpoint) { args.head :: args.tail.drop(arity) }
          else { args.drop(arity) }
        }
        assert(
          restClosureStateBTs.size == capturedValues.size,
          s"Mismatch btw ${restClosureStateBTs.mkString} and ${capturedValues.mkString}"
        )
        map2(capturedValues, restClosureStateBTs) { (captureValue, ctorParamBT) =>
          genLoad(captureValue, ctorParamBT)
        }
        // <init> invocation
        mnode.visitMethodInsn(asm.Opcodes.INVOKESPECIAL, closuInternalName, nme.CONSTRUCTOR.toString, ctorDescr)
      }

      {
        val alreadyLCC: DClosureEndpoint = closuresForDelegates.getOrElse(delegateSym, null)
        if (alreadyLCC != null) {
          log(
             "Visiting a second time a dclosure-endpoint E for which a Late-Closure-Class LCC has been created already. " +
            s"Who plays each role: E is ${delegateSym.fullLocationString} , LCC is ${alreadyLCC.closuBT.getInternalName} , " +
            s" method enclosing the closure instantation: ${methodSignature(cnode, mnode)} , position in source file: ${fakeCallsite.pos}. " +
             "This happens when duplicating an exception-handler or finally clause (which exist in two forms: " +
             "reachable-via-fall-through and reachable-via-exceptional-control-flow)."
          )
          val closuIName = alreadyLCC.closuBT.getInternalName
          emitClosureInstantiation(closuIName, alreadyLCC.closuCtor.desc)
          return castToBT
        }
      }

      /* primitive and void erase to themselves, all others (including arrays) to j.l.Object */
      def spclzdErasure(bt: BType): BType = { if (bt.isPrimitiveOrVoid) bt else ObjectReference }
      def spclzdDescriptors(bts: List[BType]): List[String] = {
        for(bt <- bts; spEra = spclzdErasure(bt))
        yield {
          if (spEra.isPrimitiveOrVoid) { spEra.getDescriptor }
          else { assert(spEra.hasObjectSort); "L" }
        }
      }

      /*
       *  initBCodeTypes() populates exemplars for all s.r.AbstractFunctionX and any specialized subclasses.
       *  We query that map to find out whether the specialization given by `key` exists.
       *
       *  @param key a string of the form $mc...$sp which may be the postfix of the internal name of
       *             an AbstractFunctionX specialized subclass.
       */
      def isValidSpclztion(key: String): Boolean = {
        val candidate = castToBT.getInternalName // `castToBT` is a non-specialized s.r.AbstractFunctionX class
        exemplarIfExisting(candidate + key) != null
      }

      /*
       *  Two cases:
       *
       *  (a) In case the closure can be specialized,
       *      the closure class to create should extend a subclass of `castToBT`,
       *      ie a subclass with name of the form s.r.AbstractFunctionX$mc...$sp ,
       *      and override an "ultimate apply()" (ie an apply method with most-specific types).
       *      Another apply-method (with "fully-erased" method signature) is also added whose task is:
       *        - unboxing arguments,
       *        - invoking the ultimate apply, and
       *        - boxing the result.
       *
       *  (b) In case the closure can't be specialized,
       *      the closure class to create extends `castToBT`, and
       *      overrides the fully-erased apply() method corresponding to the closure's arity.
       *
       *  That's what this method figures out, based on symbols inspected during initBCodeTypes()
       *
       *  @return a Pair(superClassName, list-of-overriding-methods) where:
       *
       *            - the head of the method list denotes the "ultimate-apply" override that invokes the delegate
       *
       *            - the rest are "plumbing" methods to invoke the aforementioned ultimate-apply.
       *
       *  The returned overrides are part of the closure-class being built, but the method bodies themselves are not added yet.
       */
      def takingIntoAccountSpecialization(): Pair[String, List[MethodNode]] = {

        def getUltimateAndPlumbing(key: String, mdescr: String): List[asm.tree.MethodNode] = {
          val closuIName       = castToBT.getInternalName
          val fullyErasedBT    = BT.getMethodType(ObjectReference, Array.fill(arity){ ObjectReference })
          val fullyErasedDescr = fullyErasedBT.getDescriptor
          val fullyErasedMNode = new asm.tree.MethodNode(
            asm.Opcodes.ASM4,
            (asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_FINAL),
            "apply", fullyErasedDescr,
            null, null
          )
          val plumbings: List[asm.tree.MethodNode] =
            if (mdescr == null) Nil
            else {

              assert(key    != null)
              assert(mdescr != fullyErasedDescr, "Fully-erased-apply and bridge-apply undistinguishable (same name, ie apply, same method descriptor)")

              /*
               * The 2nd plumbing method below (called simply "apply") is a so called "bridge apply", for example `int apply(int)`.
               * You might think it isn't needed, bc nobody invokes it (spclztion rewrites callsites to target the spclzd version instead)
               * HOWEVER, just because an "specialized interface" (in the example, scala.Function1$mcII$sp) declares it,
               * and s.r.AbstractFunction1$mcII$sp extends that interface, we've got to add bytecode in each subclass,
               * TODO THEREFORE a lot of boilerplate would be saved if that method were implemented in s.r.AbstractFunction1$mcII$sp already.
               */

               List(
                "apply" + key,
                "apply"
              ).map( applyName =>
                new MethodNode(
                  asm.Opcodes.ASM4,
                  (asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_FINAL),
                  applyName, mdescr,
                  null, null
                )
              )
            }

          plumbings ::: List(fullyErasedMNode)
        }

        if (arity <= 2) { // TODO for now hardcoded

          val maybeSpczld = {
            (delegateApplySection exists { bt => bt.isNonUnitValueType }) ||
            (delegateMT.getReturnType.isPrimitiveOrVoid)
          }

          if (maybeSpczld) {
            val key = {
              "$mc" +
              spclzdErasure(delegateMT.getReturnType).getDescriptor +
              spclzdDescriptors(delegateApplySection).mkString +
              "$sp"
            }
            if (isValidSpclztion(key)) {
              /* method descriptor for the "ultimate apply" ie the one with primitive types. */
              val spzldDescr: String = {
                spclzdDescriptors(delegateApplySection).mkString("(", "", ")") +
                spclzdErasure(delegateMT.getReturnType).getDescriptor
              }
              return Pair(castToBT.getInternalName + key, getUltimateAndPlumbing(key, spzldDescr))
            }
          }

        }

        val nonSpzld = castToBT.getInternalName
        assert(!nonSpzld.contains('$'), s"Unexpected specialized AbstractFunction: $nonSpzld")

        Pair(nonSpzld, getUltimateAndPlumbing(null, null))
      } // end of helper method takingIntoAccountSpecialization()


      val Pair(superClassName, ultimate :: plumbings) = takingIntoAccountSpecialization()
      val superClassBT = brefType(superClassName)

      /*
       *  A Late-Closure-Class is created as a ClassNode.
       *  Except for the apply methods everything else is added: parents, fields, and constructor.
       *
       *  The Late-Closure-Class must be public to promote inlining:
       *  that way, a method M containing an LCC instantiation can be inlined in a class of another package.
       *  A more restrictive access for LCC would limit the potential for those inlinings.
       *
       *  @return the initialized closure-class, and its only constructor.
       */
      def createAnonClosu(): Pair[asm.tree.ClassNode, asm.tree.MethodNode] = {
        val c = new asm.tree.ClassNode() // interfaces, innerClasses, fields, methods

        val simpleName = cunit.freshTypeName(
          enclClassBT.getSimpleName + nme.LCC_FUN_NAME.toString + "$" + mnode.name + "$"
        ).toString
        c.name = {
          val pak = enclClassBT.getRuntimePackage
          if (pak.isEmpty) simpleName else (pak + "/" + simpleName)
        }
        c.version   = classfileVersion
        c.access    = asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_FINAL | asm.Opcodes.ACC_SUPER // TODO is ACC_SUPER also needed?
        c.superName = superClassName

        c.interfaces.add(scalaSerializableReference.getInternalName)
        addSerialVUID(0, c)

        c.outerClass      = outerTK.getInternalName // internal name of the enclosing class of the class
        c.outerMethod     = mnode.name              // name of the method that contains the class
        c.outerMethodDesc = mnode.desc              // descriptor of the method that contains the class

        // add closure state (fields)
        for(Pair(name, bt) <- closuStateNames.zip(closuStateBTs)) {
          val fn = new FieldNode(
            asm.Opcodes.ACC_PRIVATE | asm.Opcodes.ACC_FINAL,
            name, bt.getDescriptor,
            null, null
          )
          c.fields.add(fn)
        }

        /*
         * In case the dclosure captures its outer instance the following constructor-preamble used to be emitted.
         * BUT NOT ANYMORE, because all instantiations of such dclosures occur in runtime contexts
         * where THIS is definitely not null.
         *
         * Justification for "outer-value is definitely non-null at the point of NEW dclosure":
         *   (a) when (hasOuter == true)  the enclosing method for "NEW dclosure"
         *       is an instance method (or constructor) thus THIS (ie the outer-value to dclosure)
         *       is definitely non-null.
         *   (b) when (hasOuter == false) the enclosing method for "NEW dclosure"
         *       is an implementation-class method (an impl-class derived from a non-interface trait).
         *       The outer-instance in this case is the self-value,
         *       whose type is the interface-facet of the original trait.
         *       The implementation-class method in question was invoked via forwarding from
         *       a method invoked on the self-value, ie the self-value is definitely non-null.
         *
         * TODO For "traditional" closures, rather than emitting the boilerplate above, Scala v2.11 could either:
         *        - use JDK7's java.util.Objects.requireNonNull(outer-value) which returns the argument if non-null, NPE otherwise
         *        - encapsulate that boilerplate in a scala.runtime static method.
         *
         * The preamble consisted of six instructions plus a LabelNode and used to be emitted
         * at the very beginning of the dclosure constructor built by `createClosuCtor()` :
         *     ALOAD 1
         *     IFNONNULL L0
         *     NEW java/lang/NullPointerException
         *     DUP
         *     INVOKESPECIAL java/lang/NullPointerException.<init> ()V
         *     ATHROW
         *  L1:
         *
         */
        def createClosuCtor(): asm.tree.MethodNode = {

          // registers the (possibly unseen) descriptor in Names.chrs via global.newTypeName
          val ctorDescr = BT.getMethodType(BT.VOID_TYPE, mkArray(closuStateBTs)).getDescriptor

          {
            // also registers "premonitorily" a ctor signature as above except outer is elided,
            // just in case `squashOuter()` removes it afterwards.
            // Better to do it now as this code runs single-threaded, as opposed to `squashOuter()`.
            if (hasOuter) {
              assert(closuStateBTs.nonEmpty)
              BT.getMethodType(BT.VOID_TYPE, mkArray(closuStateBTs.tail))
            }
          }

          val ctor = new asm.tree.MethodNode(
            asm.Opcodes.ASM4, asm.Opcodes.ACC_PUBLIC,
            nme.CONSTRUCTOR.toString, ctorDescr,
            null, null
          )

          def loadTHIS() { ctor.visitVarInsn(asm.Opcodes.ALOAD, 0) }

          def loadLocal(idx: Int, tk: BType) { ctor.visitVarInsn(tk.getOpcode(asm.Opcodes.ILOAD), idx) }

          /*
           *  ... init fields from params
           */
          var paramIdx = 1
          for(Pair(fieldName, fieldType) <- closuStateNames.zip(closuStateBTs)) {
            loadTHIS()
            loadLocal(paramIdx, fieldType)
            ctor.visitFieldInsn(asm.Opcodes.PUTFIELD, c.name, fieldName, fieldType.getDescriptor)
            paramIdx += fieldType.getSize
          }

          /*
           *  ALOAD 0
           *  INVOKESPECIAL scala/runtime/AbstractFunctionX.<init> ()V // or a specialized subclass
           *  RETURN
           *
           */
          loadTHIS()
          ctor.visitMethodInsn(asm.Opcodes.INVOKESPECIAL, superClassName, nme.CONSTRUCTOR.toString, "()V")
          ctor.visitInsn(asm.Opcodes.RETURN)

          // asm.optimiz.Util.computeMaxLocalsMaxStack(ctor)
          ctor
        }

        val ctor = createClosuCtor()

        Pair(c, ctor)
      } // end of method createAnonClosu()

      val Pair(closuCNode, ctor) = createAnonClosu()

      // registers the closure's internal name in Names.chrs, and let populateDClosureMaps() know about closure endpoint
      val closuBT = brefType(closuCNode.name)

      val fieldsMap: Map[String, BType] = closuStateNames.zip(closuStateBTs).toMap

      /*
       *  A plumbing-apply needs to unbox arguments before invoking the ultimate apply,
       *  and box the result ( in case Object is expected but void produced, insert scala.runtime.BoxedUnit.UNIT )
       */
      def spclzdAdapt(mnode: MethodNode, from: BType, to: BType) {
        if (from == to) { return }
        if (from.isUnitType) {
          assert(to == ObjectReference, s"Expecting j.l.Object but got: $to")
          // GETSTATIC scala/runtime/BoxedUnit.UNIT : Lscala/runtime/BoxedUnit;
          mnode.visitFieldInsn(asm.Opcodes.GETSTATIC, srBoxedUnit.getInternalName, "UNIT", srBoxedUnit.getDescriptor)
        }
        else if (to.isNonUnitValueType) {
          // must be on the way towards ultimate
          assert(from == ObjectReference, s"Expecting j.l.Object but got: $from")
          val MethodNameAndType(mname, mdesc) = asmUnboxTo(to)
          mnode.visitMethodInsn(asm.Opcodes.INVOKESTATIC, BoxesRunTime.getInternalName, mname, mdesc)
        }
        else if (from.isNonUnitValueType) {
          // must be on the way towards ultimate
          assert(to == ObjectReference, s"Expecting j.l.Object but got: $to")
          val MethodNameAndType(mname, mdesc) = asmBoxTo(from)
          mnode.visitMethodInsn(asm.Opcodes.INVOKESTATIC, BoxesRunTime.getInternalName, mname, mdesc)
        } else {
          // no need to CHECKCAST the result of a method that returns Lscala/runtime/Nothing$;
          if (!from.isNothingType) {
            assert(from.isRefOrArrayType, s"Expecting array or object type but got: $from")
            assert(to.isRefOrArrayType,   s"Expecting array or object type but got: $to")
            mnode.visitTypeInsn(asm.Opcodes.CHECKCAST, to.getInternalName)
          }
        }
      }

      /*
       *  Adds instrucitons to the ultimate-apply to invoke the delegate.
       */
      def buildUltimateBody() {
        ultimate.instructions = new asm.tree.InsnList

        def loadField(fieldName: String) {
          ultimate.visitVarInsn(asm.Opcodes.ALOAD, 0)
          val fieldType = fieldsMap(fieldName)
          ultimate.visitFieldInsn(asm.Opcodes.GETFIELD, closuCNode.name, fieldName, fieldType.getDescriptor)
        }

        def loadLocal(idx: Int, tk: BType) {
          ultimate.visitVarInsn(tk.getOpcode(asm.Opcodes.ILOAD), idx)
        }

        val ultimateMT = BT.getMethodType(ultimate.desc)

        // in order to invoke the delegate, load the receiver if any
        if (hasStaticModuleOwner) {
          // GETSTATIC the/module/Class$.MODULE$ : Lthe/module/Class;
          ultimate.visitFieldInsn(
            asm.Opcodes.GETSTATIC,
            outerTK.getInternalName /* + "$" */ ,
            strMODULE_INSTANCE_FIELD,
            outerTK.getDescriptor
          )
        }
        else if (isImplClassEndpoint) {
          loadField(closuStateNames.head)
        } else {
          if (hasOuter) { loadField(nme.OUTER.toString) }
        }

        // after that, load each apply-argument
        val callerParamsBTs = ultimateMT.getArgumentTypes.toList
        assert(callerParamsBTs.size == delegateApplySection.size)
        var idx = 1
        for(Pair(callerParamBT, calleeParamBT) <- callerParamsBTs.zip(delegateApplySection)) {
          loadLocal(idx, callerParamBT)
          spclzdAdapt(ultimate, callerParamBT, calleeParamBT)
          idx += callerParamBT.getSize
        }

        // now it only remains to load non-outer closure-state fields
        val restFieldNames = {
          if (isImplClassEndpoint) {
            closuStateNames.tail
          } else {
            if (hasOuter) closuStateNames.tail else closuStateNames
          }
        }
        for(fieldName <- restFieldNames) {
          loadField(fieldName)
          // no adapt needed because the closure-fields were derived from the delegate's params for captured valued.
        }

        val callOpc =
          if (hasOuter || hasStaticModuleOwner) asm.Opcodes.INVOKEVIRTUAL
          else asm.Opcodes.INVOKESTATIC
        ultimate.visitMethodInsn(
          callOpc,
          outerTK.getInternalName,
          delegateJavaName,
          delegateMT.getDescriptor
        )

        spclzdAdapt(ultimate, delegateMT.getReturnType, ultimateMT.getReturnType)

        ultimate.visitInsn(ultimateMT.getReturnType.getOpcode(asm.Opcodes.IRETURN))

      } // end of helper method buildUltimateBody()

      /*
       *  Emit in `caller` instructions that convey the arguments it receives
       *  to the invocation of `ultimate` (after adapting those arguments),
       *  also adapting the result before returning.
       */
      def buildPlumbingBody(caller: MethodNode) {

        caller.instructions = new asm.tree.InsnList

        def loadLocal(idx: Int, tk: BType) { caller.visitVarInsn(tk.getOpcode(asm.Opcodes.ILOAD), idx) }

        val ultimateMT = BT.getMethodType(ultimate.desc)
        val callerMT   = BT.getMethodType(caller.desc)

        // first, load the receiver (THIS)
        caller.visitVarInsn(asm.Opcodes.ALOAD, 0)

        // then, proceed to load each apply-argument
        val callerParamsBTs = callerMT.getArgumentTypes.toList
        val calleeParamsBTs = ultimateMT.getArgumentTypes.toList
        assert(callerParamsBTs.size == calleeParamsBTs.size)
        var idx = 1
        for(Pair(callerParamBT, calleeParamBT) <- callerParamsBTs.zip(calleeParamsBTs)) {
          loadLocal(idx, callerParamBT)
          spclzdAdapt(caller, callerParamBT, calleeParamBT)
          idx += callerParamBT.getSize
        }

        caller.visitMethodInsn(
          asm.Opcodes.INVOKEVIRTUAL,
          closuCNode.name,
          ultimate.name,
          ultimate.desc
        )

        spclzdAdapt(caller, ultimateMT.getReturnType, callerMT.getReturnType)

        caller.visitInsn(callerMT.getReturnType.getOpcode(asm.Opcodes.IRETURN))

      } // end of helper method buildPlumbingBody()

      buildUltimateBody()
      closuCNode.methods.add(ultimate)

      for(plumbing <- plumbings) {
        buildPlumbingBody(plumbing)
        closuCNode.methods.add(plumbing)
      }

      closuCNode.methods.add(ctor)

      log(
        sm"""genLateClosure: added Late-Closure-Class ${closuCNode.name}
            | for endpoint ${delegateJavaName}${delegateMT}
            | in class ${outerTK.getInternalName}. Enclosing method ${methodSignature(cnode, mnode)}
            | position in source file: ${fakeCallsite.pos}"""
      )

      emitClosureInstantiation(closuCNode.name, ctor.desc)

      lateClosures ::= closuCNode

      /*
       * `delegateSym` may be either:
       *   - a dclosure-endpoint created by `closureConversionModern()` in UnCurry;
       *     or
       *   - a specialized overload (created by, guess who, "specialize") for the above
       */
      closuresForDelegates.put(
        delegateSym,
        DClosureEndpoint(delegateJavaName, delegateMT, closuBT, ctor)
      )

      /*
       * There's a problem with running a Type-Flow Analysis at this point to confirm the well-formedness of `closuCNode`:
       * it's too early, because there's no guarantee the closure's endpoint has been already visited by PlainClassBuilder.
       * Until that method is visited, it's possible for its corresponding `closuCNode` to mention
       * internal names not yet registered as BTypes, and thus also not yet registered in `exemplars`.
       * Once the master class of this Late-Closure-Class has been built, that information will be available.
       */

      castToBT
    } // end of genLateClosure()

  }

}
