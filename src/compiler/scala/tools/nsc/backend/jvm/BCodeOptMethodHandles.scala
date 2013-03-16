/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.UnBoxAnalyzer.FakeParamLoad
import asm.optimiz.{SSLUtil, UnBoxAnalyzer, ProdConsAnalyzer, Util}
import asm.tree.analysis.SourceValue
import asm.tree._

import scala.collection.{ mutable, immutable }
import scala.Some
import collection.convert.Wrappers.JListWrapper
import collection.convert.Wrappers.JSetWrapper
import scala.annotation.{switch, tailrec}

/**
 *  Conversion of Late-Closure-Classes into MethodHandle-based version.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOptMethodHandles extends BCodeOptInter {

  import global._

  /**
   *  Converts each instantiation of a Late-Closure-Class into an instantiation of a MethodHandle-based AbstractFunctionX subclass.
   *  The LCC is elided. It's not necessary to check whether another class contains usages of the elided LCC
   *  (e.g., as a result of inlining) because all non-LCC ClassNodes are scanned and transformed.
   *
   *  This transformation can be applied after closure-fields have been minimized (via -neo:o3).
   *  Therefore -closurify:MH also benefits from all closure optimizations.
   *
   * */
  final class LCC2MHBased(cnode: ClassNode, mnode: MethodNode) {
    import asm.tree.analysis.{Analyzer, BasicValue, BasicVerifier}
    import asm.tree.{TypeInsnNode, MethodInsnNode, AbstractInsnNode, ClassNode}
    import asm.{Opcodes, Handle}
    import asm.optimiz.Util

    var newInsns:  List[TypeInsnNode]   = Nil
    var initInsns: List[MethodInsnNode] = Nil

    /**
     *  During `collectBrackets()` the ClassNode and BType representation of Late-Closure-Classes is found.
     *  For later use, two maps track the correspondence:
     *     LCC-internal-name to LCC-BType to LCC-ClassNode
     *  The maps cover only those LCCs found in method `mnode`
     *
     * */
    val iname2bt = mutable.Map.empty[String, BType]
    val bt2cnode = mutable.Map.empty[BType, ClassNode]

    val stream = mnode.instructions

    collectBrackets()
    assert(newInsns.size == initInsns.size)
    if(initInsns.nonEmpty) {
      rewriteBrackets()

      ifDebug {
        val da = new Analyzer[BasicValue](new asm.tree.analysis.BasicVerifier)
        da.analyze(cnode.name, mnode)
      }

    }

    /**
     *  Linear scan of the method's intructions to collect brackets of the form
     *  NEW dclosure ... INVOKESPECIAL dclosure.<init>(...)
     * */
    private def collectBrackets() {

          /**
           * Matches an "INVOKESPECIAL dclosure.<init>(...)V" instruction returning the dclosure's BType in that case. Otherwise null.
           * */
          def initOfDClosure(insn: AbstractInsnNode): BType = {
            if(insn.getOpcode == Opcodes.INVOKESPECIAL) {
              val mi = insn.asInstanceOf[MethodInsnNode]
              if(mi.name == "<init>") {
                val dbt = iname2bt.getOrElse(mi.owner, null)
                return dbt
              }
            }

            null
          }

      val iter = stream.iterator()
      while(iter.hasNext) {
        val i = iter.next()

        var dbt: BType = closuRepo.instantiatedDClosure(i)
        if(dbt != null) {
          val ti = i.asInstanceOf[TypeInsnNode]
          newInsns ::= ti
          iname2bt.put(ti.desc, dbt)
          val dCNode = codeRepo.classes.get(dbt)
          assert(dCNode != null)
          bt2cnode.put(dbt, dCNode)
        }
        else {
          dbt = initOfDClosure(i)
          if(dbt != null) {
            val mi = i.asInstanceOf[MethodInsnNode]
            initInsns ::= mi
          }
        }
      }

    } // end of method collectBrackets()

    /**
     *  Start situation:
     *  ----------------
     *
     *     NEW LCC
     *     DUP
     *     . . . instructions that load closure-state values
     *     INVOKESPECIAL LCC.<init>
     *
     *  After rewriting:
     *  ----------------
     *
     *     NEW scala.runtime.MHAbsFunX
     *     DUP
     *     . . . instructions that load closure-state values
     *     . . . LDC of MethodHandle constant
     *     . . . instructions to bind the closure-state, returning a new MH
     *     INVOKESPECIAL scala.runtime.MHAbsFunX.<init>
     *
     * */
    private def rewriteBrackets() {

      val binfo: collection.Map[String, ClosuBindUtil] = iname2bt map { case Pair(iname, dbt) =>
        Pair(iname, new ClosuBindUtil(dbt, bt2cnode(dbt)))
      }

      for(ni <- newInsns) {
        ni.desc = binfo(ni.desc).mhAbsFunName
      }

      for(ini <- initInsns) {
        val bi = binfo(ini.owner)
        bi.rewriteInit(ini, mnode)
      }

      Util.computeMaxLocalsMaxStack(mnode)

    }

  } // end of class LCC2MHBased

  /**
   *  Distilled information about an LCC, information useful when binding arguments to a MethodHandle instance.
   *
   *  @param dbt    Late-Closure-Class, as BType
   *  @param dCNode the same Late-Closure-Class, as ClassNode
   * */
  private class ClosuBindUtil(dbt: BType, dCNode: ClassNode) {

    val epMRef:  MethodRef  = closuRepo.endpoint.get(dbt)
    val epOwner: BType      = epMRef.ownerClass
    val epMN:    MethodNode = epMRef.mnode
    val epMT:    BType      = BType.getMethodType(epMN.desc)

        /**
         * Of the many apply() methods emitted for an LCC,
         * the one with the fewest boxing/unboxing is that with the longest name (specialization dixit).
         * */
        def lookupUltimate(): MethodNode = {
          var res: MethodNode = null
          val iterM = dCNode.methods.iterator()
          while(iterM.hasNext) {
            val m = iterM.next()
            if(m.name.startsWith("apply")) {
              if(res == null) { res = m }
              else {
                if(m.name.length > res.name.length) {
                  res = m
                }
              }
            }
          }

          res
        }

    val ultimate: MethodNode = lookupUltimate()
    Util.computeMaxLocalsMaxStack(ultimate)

    val ultimateMT   = BType.getMethodType(ultimate.desc)
    val arity        = ultimateMT.getArgumentCount
    val isEpInstance = Util.isInstanceMethod(epMN)

    val mhAbsFunName = ("scala/runtime/MHAbsFun" + arity)

    /**
     *  The apply() of interest ("ultimate") invokes the endpoint ("epMN") with arguments produced by either:
     *    - a LOAD_param instruction, ie not a captured value
     *    - a GETFIELD   instruction, ie a captured value received as LCC constructor value. In particular $outer.
     *    - a GETSTATIC  instruction, in case the endpoint is owned by a static module.
     *                   Rather than passing the (known) static module as $outer, `genLateClosure()`
     *                   emits an apply() method directly accessing it via GETSTATIC.
     *                   This value can be consumed only in the receiver position of the callsite that targete the endpoint.
     *
     *  By inspecting the apply() method, "slots" in the `bindSlots` array are filled according to the pattern:
     *    - String       denotes a field name
     *    - null         an apply() param. The corresponding "slot" in the MethodHandle won't be bound.
     *
     *  A GETSTATIC if present (denoting the receiver of the endpoint invocation) is recorded separately, see `gs`
     *  
     *  Each index of `bindSlots` corresponds to the "pos" parameter of
     *  j.l.i.MethodHandles.insertArguments(MethodHandle target, int pos, Object... values)
     *
     * */
    val bindSlots = {
      val argCount = epMT.getArgumentCount
      val n        = if(isEpInstance) { argCount + 1 } else { argCount }

      new Array[String](n)
    }

        /**
         *  Is instruction `i` a callsite targeting method `callee` (where `callee` is defined in class `calleeOwner`).
         * */
        def isCallsiteTargeting(i: AbstractInsnNode, calleeOwner: BType, callee: MethodNode): Boolean = {
          i.getType == AbstractInsnNode.METHOD_INSN && {
            val mi = i.asInstanceOf[MethodInsnNode]

            (mi.name == callee.name) && (mi.desc == callee.desc) && (mi.owner == calleeOwner.getInternalName)
          }
        }

        /**
         *  Returns the instruction in the LCC's apply() that invokes the LCC's endpoint. 
         * */
        def lookupEPCallsite(): MethodInsnNode = {
          val iter = ultimate.instructions.iterator()
          while(iter.hasNext) {
            val i = iter.next()
            if(isCallsiteTargeting(i, epOwner, epMN)) {
              return i.asInstanceOf[MethodInsnNode]
            }
          }
          abort("Couldn't find the endpoint callsite in an LCC's apply()")
        }

    /**
     *  Callsite in the LCC's apply() that invokes the LCC's endpoint. 
     * */
    val epCallsite = lookupEPCallsite()

    /**
     *  The receiver of an instance-endpoint on static module isn't available as closure-field.
     *  `gs` gets assigned a clone of the GETSTATIC instructions that loads a static module instance,
     *  in case the LCC makes use of it.
     * */
    var gs: FieldInsnNode = null

        /**
         *  @see the `bindSlots` array.
         * */
        def populateBindSlots() {
          val cp: ProdConsAnalyzer = ProdConsAnalyzer.create()
          cp.analyze(dCNode.name, ultimate)

          val f   = cp.frameAt(epCallsite)
          var idx = 0

              @tailrec def markSlot(srcInsns: _root_.java.util.Set[AbstractInsnNode]) {
                // a single producer-instruction is expected
                assert(srcInsns.size() == 1)
                val s = srcInsns.iterator().next()
                if(Util.isLOAD(s)) { return }
                if((s.getOpcode == Opcodes.CHECKCAST) || SSLUtil.isScalaUnBox(s) || SSLUtil.isScalaBox(s)) {
                  // we're interested in the "real source", thus go after its producer
                  // TODO java (un)box not emitted by GenBCode's genLateClosure()'s spclzdAdapt()
                  markSlot(cp.producers(s))
                } else {
                  assert(bindSlots(idx) == null)
                  if(s.getOpcode == Opcodes.GETSTATIC) {
                    // for example, GETSTATIC scala/reflect/io/Path$.MODULE$ : Lscala/reflect/io/Path$;
                    assert(idx == 0)
                    val fi = s.asInstanceOf[FieldInsnNode]
                    assert(gs == null)
                    gs = new FieldInsnNode(Opcodes.GETSTATIC, fi.owner, fi.name, fi.desc)
                  } else {
                    assert(s.getOpcode == Opcodes.GETFIELD)
                    val fi = s.asInstanceOf[FieldInsnNode]
                    assert(fi.owner == dCNode.name)
                    bindSlots(idx) = fi.name
                  }
                }
              }

          if(isEpInstance) {
            val rcvSrc = f.getReceiver(epCallsite)
            markSlot(rcvSrc.insns)
            idx += 1
          }
          for(argSrc <- f.getActualArguments(epCallsite)) {
            markSlot(argSrc.insns)
            idx += 1
          }
        }

    populateBindSlots()

    /**
     *  Given a field name, the `fname2bndidx` map informs under which index the field's value
     *  should be bound in the MethodHandle for the endpoint.
     *  In case the field's value shouldn't be bound, this map contains no entry for it.
     *  Currently LCCs are emitted in such a way that all closure-state fields not removed by `minimizeDClosureFields()`
     *  provide values in an endpoint invocation. However `ClosuBindUtil` can also cope with (some future) situation
     *  where that might not be the case.
     * */
    val fname2bndidx = (
      for(Pair(cell, bndidx) <- bindSlots.zipWithIndex; if cell != null)
      yield Pair(cell.asInstanceOf[String], bndidx)
    ).toMap

    val ctor   = dCNode.toMethodList.find(m => Util.isConstructor(m)).get
    val ctorMT = BType.getMethodType(ctor.desc)
    assert(ctor.name == "<init>")
    Util.computeMaxLocalsMaxStack(ctor)

    val txtCtor = Util.textify(ctor) // debug

        /**
         *  The constructor of a closure-class copies param values (ie captured values)
         *  into closure-fields (ie closure-state).
         *
         *  This method informs which param (given by its zero-based index, "ctorpos",
         *  has its value copied to which field (given by its name).
         *
         *  Currenly no LCC is emitted such that a ctor-param isn't copied to a closure-field.
         *  But the producers-consumers analysis below could cope with that situation.
         *  In that case there would be no entry for such param.
         * */
        def trackCtorParamsFlow(): collection.Map[Int, String] = {
          val result = mutable.Map.empty[Int, String]

          val cp: ProdConsAnalyzer = ProdConsAnalyzer.create()
          cp.analyze(dCNode.name, ctor)

              def walkBackToParamLoad(srcs: _root_.java.util.Set[AbstractInsnNode]): Int = {
                val paramLoad = {
                  JSetWrapper(srcs) collect { case vi: VarInsnNode if vi.`var` > 0 => vi.`var` }
                }
                paramLoad.head
              }

          ctor.foreachInsn { insn =>
            if(insn.getOpcode == Opcodes.PUTFIELD) {
              val fi       = insn.asInstanceOf[FieldInsnNode]
              val localIdx = walkBackToParamLoad(cp.producers(fi))
              val ctorpos  = ctorMT.convertLocalVarIdxToFormalParamPos(localIdx, isInstanceMethod = true)
              result.put(ctorpos, fi.name)
            }
          }

          result
        }

    val ctorpos2fname: collection.Map[Int, String] = trackCtorParamsFlow()

    /**
     *  @see `rewriteBrackets()`
     * */
    def rewriteInit(ini: MethodInsnNode, mnode: MethodNode) {

      val snippet = new InsnList

      // ------- (1) load the MH-constant for the endpoint, initially with no params bound, no receiver bound either.
      val ldc = {
        val tag    = if(isEpInstance) Opcodes.H_INVOKEVIRTUAL else Opcodes.H_INVOKESTATIC
        val handle = new asm.Handle(tag, epOwner.getInternalName, epMN.name, epMN.desc)
        new LdcInsnNode(handle)
      }
      snippet.add(ldc)

      // ------- (2) empty the arguments, from last to first, by binding or dropping.
      val ctorMT      = BType.getMethodType(ctor.desc)
      val ctorArgsBTs = ctorMT.getArgumentTypes
      for(ctorpos <- (ctorMT.getArgumentCount - 1) to 0 by -1) {
        val bndidx = {
          val fname = ctorpos2fname.getOrElse(ctorpos, null)
          fname2bndidx.getOrElse(fname, -1)
        }
        val ctorArgBT = ctorArgsBTs(ctorpos)
        val ctorArgDesc =
          if(ctorArgBT.isValueType) ctorArgBT.getDescriptor else ObjectReference.getDescriptor

        val mhUtilBindAtDesc =
          s"(${ctorArgDesc}Ljava/lang/invoke/MethodHandle;I)Ljava/lang/invoke/MethodHandle;"

        val mhUtilBindAt = new MethodInsnNode(
          Opcodes.INVOKESTATIC,
          "scala/runtime/MHUtil",
          "bindAt",
          mhUtilBindAtDesc
        )

        snippet.add(new LdcInsnNode(_root_.java.lang.Integer.valueOf(bndidx)))

        snippet.add(mhUtilBindAt)
      }

      // ------- (3) The receiver of an instance-endpoint on static module isn't available as closure-field
      if(gs != null) {
        snippet.add(gs)
        val mhBindTo = new MethodInsnNode(
          Opcodes.INVOKEVIRTUAL,
          "java/lang/invoke/MethodHandle",
          "bindTo",
          "(Ljava/lang/Object;)Ljava/lang/invoke/MethodHandle;"
        )
        snippet.add(mhBindTo)
      }

      // ------- (4) rewriting proper
      mnode.instructions.insertBefore(ini, snippet)
      ini.owner = mhAbsFunName
      ini.desc  = "(Ljava/lang/invoke/MethodHandle;)V"

    } // end of method rewriteInit()

  } // end of class ClosuBindUtil

} // end of class BCodeOptMethodHandles
