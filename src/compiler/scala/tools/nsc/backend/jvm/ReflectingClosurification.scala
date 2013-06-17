/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala
package tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.Util
import asm.tree._

import scala.collection.{ mutable, immutable }
import scala.Some
import scala.annotation.switch

/*
 *  Rewrite a class originally enclosing anon-closures to use Reflection-Based (anonymous) Closures ("RBC" for short).
 *
 *  Dedicating a classfile to each anon-closure increases code size, even after closure inlining.
 *  Instead, an anon-closure can be represented as an `scala.runtime.ReflBasedFun...` instance,
 *  customized via arguments. The downside is the reflective method call
 *  (targeting the dclosure's endpoint) on each `apply()` invocation.
 *
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class ReflectingClosurification extends BCodeOptClosu {

  import global._

  /*
   *  Transformations performed so far affecting LCCs
   *  -----------------------------------------------
   *
   *  The conversion for Reflection-based Closures ("RBCs" for short) takes as starting point (possibly optimized) LCCs.
   *  Let's recap what those LCCs look like by the time `ReflectingClosurifier` gets to transform them.
   *
   *  Under `-closurify:reflect` the following is skipped:
   *    (s.1) `singletonizeDClosures()` and
   *    (s.2) `minimizeDClosureFields()`
   *  because the customizations they perform (in particular eliding apply-args on the part of `minimizeDClosureFields()`)
   *  are cumbersome to achieve with `scala.runtime.ReflBasedFun...` classes
   *  (which aren't customized on a per-delegate basis as LCCs are).
   *
   *  No other optimization is skipped,
   *  ie they may have run (before `ReflectingClosurifier`) subject to the chosen optimization level.
   *  In particular:
   *    (k.1) `squashOuterForLCC()` runs by default
   *    (k.2) `staticMaker` (which makes static when possible lifted-methods, including LCC delegates)
   *           has run (in case -neo:o1 or higher was chosen).
   *    (k.3) inlining has run (in case -neo:o2 or higher was chosen)
   *          As a consequence, an LCC instantiation may occur in any non-LCC class,
   *          not just on the class that originally enclosed it.
   *
   *
   *  Two varieties of Reflection-based Closures: M-style and R-style
   *  ---------------------------------------------------------------
   *
   *  A usage site that obtains an LCC instance is rewritten to instantiate instead an `scala.runtime.ReflBasedFun...`.
   *  A ReflBasedFun can be one of:
   *
   *    (1) M-style:
   *        ie one of `scala.runtime.ReflBasedFunM<arity>`
   *        For a delegate owned by an implementation-class
   *        One such delegate is characterized by:
   *          - it's static,
   *          - the self-reference of the mixin is the first argument,
   *          - followed by the apply-arguments,
   *          - followed by any non-outer captured vaules.
   *        Additionally, the delegate is always static.
   *
   *    (2) R-style:
   *        ie one of `scala.runtime.ReflBasedFunR<arity>`
   *        For any delegate not owned by an implementation-class, where the delegate may be instance or static.
   *        Whether instance or static:
   *          - the first arity arguments to the delegate are the apply() arguments,
   *          - followed by any non-outer captured values.
   *
   *
   *  Static members added to a class declaring delegates
   *  ---------------------------------------------------
   *
   *  (a) For each dclosure-endpoint owned by `cnode`,
   *      a public static field holding the `java.lang.reflect.Method` for the endpoint in question is added to `cnode`.
   *      The cost of looking up via `getDeclaredMethod()` is incurred just once
   *      (according to folklore, that lookup is expensive, while reflective invocations are comparatively less expensive).
   *
   *  (b) Factories of `ReflBasedFun...` instances are also added to `cnode`.
   *      Each factory method receives as arguments the values captured by the dclosure
   *        and returns an `scala.runtime.ReflBasedFun...` instance.
   *
   *  The static fields in (a) are initialized at the very start of cnode's <clinit>.
   *  In theory, after that prolog, reflect-based anon-closures could be used in <clinit> itself.
   *
   *  @param cnode    a class that's responsible for one or more dclosures
   *  @param masterBT the BType for cnode
   *  @param dcs      non-elided dclosures for which cnode is responsible
   *
   */
  final class ReflectingClosurifier(val cnode: ClassNode, val cnodeBT: BType, val dcs: List[BType])
    extends ReflectiveCaching
       with ReflectiveFactories {

    assert(isReflectClosuresOn)

    def getReflFunCtorDescr(isM: Boolean): String = {
      if (isM) "(Ljava/lang/reflect/Method;[Ljava/lang/Object;)V"
      else     "(Ljava/lang/reflect/Method;Ljava/lang/Object;[Ljava/lang/Object;)V"
    }

    // add static class initializer if not there
    val clinit: MethodNode = {
      cnode.toMethodList.find(_.name == "<clinit>") match {

        case None  =>
          val staticClassInitializer =
            new MethodNode(
              Opcodes.ASM4,
              Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC,
              "<clinit>",
              "()V",
              null, null
            )
          staticClassInitializer.visitInsn(Opcodes.RETURN)
          cnode.methods.add(staticClassInitializer)
          staticClassInitializer

        case Some(found) => found
      }
    }

    for(dc <- dcs) {
      val ep = closuRepo.endpoint.get(dc).mnode
      reflectiveCache(ep, dc)
      reflectiveFactory(ep, dc)
    }
    Util.computeMaxLocalsMaxStack(clinit)

  }

  /*
   * For each endpoint, a static field caches its j.l.r.Method.
   * That field is initialized in <clinit> via:
   *
   *   <cnode-class>.getDeclaredMethod(<endpoint-name>, j.l.Class for each formal-param of the endpoint)
   */
  trait ReflectiveCaching { _: ReflectingClosurifier =>

    def reflFieldName(ep: MethodNode) = (ep.name + "reflDelegate$")

    def reflectiveCache(ep: MethodNode, dc: BType) {
      val fn = fieldForEndpoint(ep)
      cnode.fields.add(fn)
      val initInsns = fieldInitializer(fn, dc, ep)
      clinit.instructions.insert(initInsns)
    }

    def fieldForEndpoint(ep: MethodNode): FieldNode = {
      new FieldNode(
        asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_FINAL | asm.Opcodes.ACC_STATIC,
        reflFieldName(ep),
        jlrMethod.getDescriptor,
        null, null
      )
    }

    def fieldInitializer(fn: FieldNode, dc: BType, ep: MethodNode): InsnList = {
      val epBT = BMType(ep.desc)
      val mn   = new MethodNode()
      mn.visitLdcInsn(cnodeBT.toASMType)
      mn.visitLdcInsn(ep.name)
      iconst(mn, epBT.getArgumentCount)
      mn.visitTypeInsn(Opcodes.ANEWARRAY, jlClass.getInternalName)
      var idx = 0
      while(idx < epBT.argumentTypes.length) {
        mn.visitInsn(Opcodes.DUP)
        iconst(mn, idx)
        mn.instructions.add(loadClassOf(epBT.argumentTypes(idx)))
        mn.visitInsn(Opcodes.AASTORE)
        idx += 1
      }
      mn.visitMethodInsn(
        Opcodes.INVOKEVIRTUAL,
        jlClass.getInternalName,
        "getDeclaredMethod",
        "(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;"
      )
      mn.visitFieldInsn(Opcodes.PUTSTATIC, cnode.name, fn.name, fn.desc)
      mn.instructions
    }

    def loadClassOf(bt: BType): AbstractInsnNode = {
      (bt.sort: @switch) match {
        case asm.Type.ARRAY  | asm.Type.OBJECT =>
          new LdcInsnNode(bt.toASMType)
        case asm.Type.METHOD  =>
          throw new RuntimeException("The intended representation for bytecode-level method-types is BMType, not BType.")
        case _  =>
          val cl = classLiteral(bt)
          new FieldInsnNode(Opcodes.GETSTATIC, cl.getInternalName, "TYPE", jlClass.getDescriptor)
      }
    }

  } // end of trait ReflectiveCaching

  /*
   * For each endpoint, a static factory method is added to `cnode`.
   * It will be invoked at runtime to obtain an RBC.
   */
  trait ReflectiveFactories { _: ReflectingClosurifier =>

    def reflectiveFactory(ep: MethodNode, dc: BType) {
      val isM       = isMStyle(dc)
      val factoryMT = reflFactoryMethodType(dc, isM)

      val factory = new MethodNode(
        asm.Opcodes.ACC_PUBLIC | asm.Opcodes.ACC_STATIC,
        reflFactoryName(ep),
        factoryMT.getDescriptor,
        null, null
      )

      // NEW ReflFun{R|M}X; DUP
      val reflClosu = factoryMT.returnType
      factory.visitTypeInsn(Opcodes.NEW, reflClosu.getInternalName)
      factory.visitInsn(Opcodes.DUP)

      // 1st constructor arg (mandatory): j.l.r.Method for the endpoint
      val epOwner: BType = closuRepo.endpoint.get(dc).ownerClass
      factory.visitFieldInsn(
        Opcodes.GETSTATIC,
        epOwner.getInternalName,
        reflFieldName(ep),
        jlrMethod.getDescriptor
      )

      // for R-style reflection-based closures, instructions are emitted to load the receiver
      var formalIdx = 0 // `formalIdx` indicates the next available local-idx (standing for a formal, in a static (factory) method).
      if (!isM) {
        if (Util.isStaticMethod(ep)) {
          // null receiver
          factory.visitInsn(Opcodes.ACONST_NULL)
        } else if (isOwnedByStaticModule(dc)) {
          // GETSTATIC the/module/Class$.MODULE$ : Lthe/module/Class;
          factory.visitFieldInsn(
            Opcodes.GETSTATIC,
            epOwner.getInternalName /* + "$" */ ,
            strMODULE_INSTANCE_FIELD,
            epOwner.getDescriptor
          )
        } else {
          factory.visitVarInsn(Opcodes.ALOAD, 0)
          formalIdx = 1
        }
      }

      // emit instructions to load the args array,
      // the array to use in the body of the closure: `j.l.r.Method.invoke(receiver, args)`
      val epMT       = BMType(ep.desc)
      val epArgCount = epMT.getArgumentCount
      iconst(factory, epArgCount)
      factory.visitTypeInsn(Opcodes.ANEWARRAY, ObjectReference.getInternalName)

      // M-style requires the first elem of `args` to be the self-reference of the mixin.
      var arrIdx = 0 // `arrIdx` indicates the next available slot in the `args` array to populate via insns being emitted.
      if (isM) {
        // the array
        factory.visitInsn(Opcodes.DUP)
        // index of the element in the array
        factory.visitInsn(Opcodes.ICONST_0)
        // we're in a static (factory) methods, thus 0 is the slot of the first argument, standing for the self-reference
        factory.visitVarInsn(Opcodes.ALOAD, 0)
        factory.visitInsn(Opcodes.AASTORE)
        arrIdx = 1
        formalIdx = 1
      }

      // a total of arity elements in the `args` array will be populated by the apply() of the refl-based closure.
      val ari = arity(dc)
      arrIdx += ari

      // emit instructions to assign each factory-argument to a slot in the `args` array
      while (arrIdx < epArgCount) {
        // the array
        factory.visitInsn(Opcodes.DUP)
        // index of the element in the array
        iconst(factory, arrIdx)
        // the type of the formalIdx-th formal-param
        val formalT = factoryMT.argumentTypes(formalIdx)
        // load that formal-param
        val localIdxForParam = factoryMT.convertFormalParamPosToLocalVarIdx(paramPos = formalIdx, isInstanceMethod = false)
        factory.visitVarInsn(formalT.getOpcode(Opcodes.ILOAD), localIdxForParam)
        // box if needed
        if (formalT.isNonUnitValueType) {
          val MethodNameAndType(mname, mdesc) = asmBoxTo(formalT)
          factory.visitMethodInsn(Opcodes.INVOKESTATIC, BoxesRunTime.getInternalName, mname, mdesc)
        }
        // store in the arrIdx-slot of the `args` array
        factory.visitInsn(Opcodes.AASTORE)
        arrIdx    += 1
        formalIdx += 1
      }
      assert(formalIdx == factoryMT.argumentTypes.length)

      // <init> of ReflFun{R|M}X
      factory.visitMethodInsn(
        Opcodes.INVOKESPECIAL,
        reflClosu.getInternalName,
        nme.CONSTRUCTOR.toString,
        getReflFunCtorDescr(isM)
      )

      factory.visitInsn(Opcodes.ARETURN)

      cnode.methods.add(factory)
      Util.computeMaxLocalsMaxStack(factory)

      ifDebug {
        val ec = new EssentialCleanser(cnode)
        ec.runTypeFlowAnalysis(factory)
      }

    }

    final def iconst(mnode: MethodNode, cst: Int) {
      if (cst >= -1 && cst <= 5) {
        mnode.visitInsn(Opcodes.ICONST_0 + cst)
      } else if (cst >= java.lang.Byte.MIN_VALUE && cst <= java.lang.Byte.MAX_VALUE) {
        mnode.visitIntInsn(Opcodes.BIPUSH, cst)
      } else if (cst >= java.lang.Short.MIN_VALUE && cst <= java.lang.Short.MAX_VALUE) {
        mnode.visitIntInsn(Opcodes.SIPUSH, cst)
      } else {
        mnode.visitLdcInsn(new Integer(cst))
      }
    }

    def isOwnedByStaticModule(dc: BType): Boolean = {
      val epOwner: BType = closuRepo.endpoint.get(dc).ownerClass
      codeRepo.classes.get(epOwner).isStaticModule
    }

  } // end of trait ReflectiveFactories

  def reflFactoryName(ep: MethodNode): String = (ep.name + "reflFactory$")

  def arity(dc: BType): Int = {
    val dCNode   = codeRepo.classes.get(dc)
    val appMNode = dCNode.toMethodList.find(_.name.startsWith("apply")).get
    BMType(appMNode.desc).getArgumentCount
  }

  /*
   *  A ReflBasedFun can be either M-style or R-style.
   *
   *  M-style corresponds to a dclosure whose delegate is owned by an implementation-class.
   *  Such delegate is characterized by:
   *    - it's static,
   *    - the self-reference of the mixin is the first argument,
   *    - followed by the apply-arguments,
   *    - followed by any non-outer captured vaules.
   */
  def isMStyle(dc: BType): Boolean = {
    val MethodRef(epOwner, ep) = closuRepo.endpoint.get(dc)
    if (Util.isInstanceMethod(ep)) return false;
    if (arity(dc) == 0) return false;
    val dCNode = codeRepo.classes.get(dc)

    def getApplyWithStaticDelegateCall: MethodNode = {

      def isStaticDelegateInvocation(mi: MethodInsnNode) = (
        mi.getOpcode == Opcodes.INVOKESTATIC &&
        mi.owner == epOwner.getInternalName  &&
        mi.name  == ep.name
      )

      val candidates =
        for(
          closuMethod <- dCNode.toMethodList;
          if closuMethod.name.startsWith("apply");
          if closuMethod.toList.exists {
            case mi: MethodInsnNode => isStaticDelegateInvocation(mi)
            case _                  => false
          }
        ) yield closuMethod;

      candidates match {
        case theOne :: Nil => theOne
        case _             => null
      }
    }

    val applyWithStaticDelegateCall = getApplyWithStaticDelegateCall
    if (applyWithStaticDelegateCall == null) return false;

    def isFirstCtorParam(name: String): Boolean = dCNode.toFieldList.filter(Util.isInstanceField) match {
      case fst :: _ => fst.name == name
      case _        => false
    }

    def isGetFieldOfFirstCtorParam(fi: FieldInsnNode): Boolean = (fi.getOpcode == Opcodes.GETFIELD && isFirstCtorParam(fi.name))

    def isLoadOfFirstCtorParam(i1: AbstractInsnNode, i2: AbstractInsnNode): Boolean = {
      (i1, i2) match {
        case (load: VarInsnNode, fi: FieldInsnNode) =>
          load.`var` == 0 && isGetFieldOfFirstCtorParam(fi)
        case _ => false
      }
    }

    applyWithStaticDelegateCall.toList.filter(Util.isExecutable) match {
      case i1 :: i2 :: _ =>
        // ie rather than the first apply-arg, the first arg of the delegate-invocation is the self-ref of the mixin.
        isLoadOfFirstCtorParam(i1, i2)
      case _             => false
    }
  }

  def reflFactoryMethodType(dc: BType, isM: Boolean): BMType = {
    val dCNode = codeRepo.classes.get(dc)
    val ctor   = dCNode.toMethodList.find(_.name == nme.CONSTRUCTOR.toString).get
    val argTs  = BMType(ctor.desc).argumentTypes
    val retT   = (if (isM) ReflBasedFunMReference else ReflBasedFunRReference)(arity(dc)).c
    BMType(retT, argTs)
  }

  /*
   *  Rewrite usages of LCCs into reflection-based closures
   *  -----------------------------------------------------
   *
   *  On entry to this transformation, a Late-Closure is obtained via:
   *
   *    NEW LCC; DUP; ...load captured values if any...; INVOKESPECIAL LCC.<init>
   *
   *  After rewriting to use RBC:
   *    - both NEW and DUP are removed
   *    - the instructions to load captured values (aka closure-state) are left in place
   *    - the above arguments are consumed by a (static) factory invocation, which replaces the INVOKESPECIAL <init>.
   *
   *  Sidenote: another way to obtain a Late-Closure results from `singletonizeDClosures()`
   *            where a GETSTATIC LCC.$single appears instead of the idiom `NEW LCC, etc`
   *            But given `singletonizeDClosures()` is disabled under -closurify:reflect , no such GETSTATIC is found.
   *
   */
  final class ReflClosuUsages(val cnode: ClassNode) {

    assert(isReflectClosuresOn)
    assert(!closuRepo.isDelegatingClosure(cnode))

    for(
      mnode <- cnode.toMethodList;
      if Util.hasBytecodeInstructions(mnode);
      insn  <- mnode.toList
    ) {
      insn match {

        case ti: TypeInsnNode =>
          val dc = closuRepo.instantiatedDClosure(ti)
          if (dc != BT_ZERO) {
            assert(ti.getNext.getOpcode == Opcodes.DUP)
            mnode.instructions.remove(ti.getNext)
            mnode.instructions.remove(ti)
          }

        case init: MethodInsnNode =>
          val dc = closuRepo.initializedDClosure(init)
          if (dc != BT_ZERO) {
            mnode.instructions.set(init, reflFactoryCall(dc, init))
          }

        case _ => ()
      }
    }

    def reflFactoryCall(dc: BType, init: MethodInsnNode): MethodInsnNode = {
      val MethodRef(epOwner, ep) = closuRepo.endpoint.get(dc)

      val isM       = isMStyle(dc)
      val factoryMT = reflFactoryMethodType(dc, isM)

      new MethodInsnNode(
        asm.Opcodes.INVOKESTATIC,
        epOwner.getInternalName,
        reflFactoryName(ep),
        factoryMT.getDescriptor
      )
    }

  }

}

// TODO pre-register [Ljava/lang/Class;
// TODO pre-register [Ljava/lang/Object;
// TODO those BMTypes like ()V that were pre-registered (also for StringBuffer) not needed anymore: ONLY THEIR CONSTITUENTS
// log and debuglog