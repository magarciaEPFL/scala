/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.{ProdConsAnalyzer, UnBoxAnalyzer, Util}
import asm.tree.analysis.SourceValue
import asm.tree._

import scala.collection.{ mutable, immutable }
import scala.Some
import collection.convert.Wrappers.JListWrapper
import collection.convert.Wrappers.JSetWrapper

/*
 *  Utilities shared across intra-method and inter-procedural optimizations.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOptCommon extends BCodeTypes {

  trait BCodeCleanserIface {
    def intraMethodFixpoints(full: Boolean)
  }

  case class MethodRef(ownerClass: BType, mnode: MethodNode)

  /*
   * Terminology for delegating closures
   * -----------------------------------
   *
   * "delegating closure": ("dclosure" for short) an anonymous-closure-class
   *                       created by UnCurry's `closureConversionModern()`.
   *
   * "dclosure endpoint":  method consisting of the closure's body, its name contains "dlgt$".
   *
   * "master class of a dclosure": non-dclosure class declaring one or more dclosure endpoints
   *                               (we say the master class "is responsible for" its dclosures).
   *
   * Invariants for delegating closures
   * ----------------------------------
   *
   * These invariants are checked in `checkDClosureUsages()`
   *
   * The items above exhibit invariants that a "traditional closure" doesn't necessarily guarantee,
   * invariants that can be exploited for optimization:
   *
   *   (a) the endpoint of a dclosure is the single entry point through which
   *       the dclosure may access functionality of its master class.
   *
   *   (b) Initially there's program wide a single callsite targeting any given dclosure-endpoint
   *       (that callsite is enclosed in one of the dclosure's apply() methods).
   *       This may change due to:
   *
   *         (b.1) dead-code elimination, which may remove the instantiation of the dclosure
   *
   *         (b.2) as part of `WholeProgramAnalysis.inlining()`, closure-inlining elides a dclosure-class.
   *               As a result, one or more callsites to the endpoint may occur now in the
   *               "static-HiO" method added to the master class (see `buildStaticHiO`).
   *               Still, all those occurrences can be found by inspecting the master class.
   *               Moreover, a static-HiO method, although public, is itself never inlined
   *               (callsites to it may well be inlined, e.g. in another class).
   *               Thus the following invariant holds:
   *
   *               Callsites to a dclosure endpoint may appear only:
   *                 - either in
   *                     the dclosure (just one callsite), if the dclosure hasn't been inlined;
   *                 - or
   *                     in the master class (one ore more callsites), if the dclosure has been inlined.
   *
   *               (This whole nit-pick about not losing track of callsites to endpoints is
   *               justified by our desire to optimize).
   *
   *   (c) a class C owning a closure-endpoint method isn't a delegating-closure itself
   *       (it's fine for C to be a traditional-closure or a non-closure).
   *
   * Beware
   * ------
   *
   *   (1) Not really an invariant but almost:
   *       "all instantiations of dclosure D are enclosed in a method of the master class of D"
   *       With inlining, "transplanting" a method's instructions to another class may break the property above.
   *
   *
   *   (2) Care is needed to preserve Invariant (b.2) in the presence of closure-inlining and delayedInit,
   *       ie we want to preserve:
   *             static-HiO's declaring class == master class of the inlined dclosure
   *
   *   (3) Just like with "traditional" anonymous closures, a dclosure may be instantiated
   *       at several program-points. This contradics what source-code suggests, and results
   *       from the way catch-clauses and finally-clauses are represented in bytecode
   *       (they are duplicated, one each for normal and exceptional control-flow,
   *       details in `GenBCode` in particular `genSynchronized()` , `genLoadTry()` , `emitFinalizer()`).
   *
   */
  object closuRepo extends BCInnerClassGen {

    /*
     *  dclosure-class -> endpoint-as-methodRef-in-master-class
     *
     *  @see populateDClosureMaps() Before that method runs, this map is empty.
     */
    val endpoint = new java.util.concurrent.ConcurrentHashMap[BType, MethodRef]

    /*
     *  master-class -> dclosure-classes-it's-responsible-for
     *
     *  @see populateDClosureMaps() Before that method runs, this map is empty.
     */
    val dclosures = new java.util.concurrent.ConcurrentHashMap[BType, List[BType]]

    // --------------------- query methods ---------------------

    def isDelegatingClosure( c:    BType):     Boolean = { endpoint.containsKey(c) }
    def isDelegatingClosure(iname: String):    Boolean = { isDelegatingClosure(lookupRefBType(iname)) }

    def clear() {
      endpoint.clear()
      dclosures.clear()
    }

  } // end of object closuRepo

  override def clearBCodeOpt() {
    closuRepo.clear()
  }

  /*
   * @param mnode a MethodNode, usually found via codeRepo.getMethod(bt: BType, name: String, desc: String)
   * @param owner ClassNode declaring mnode
   */
  case class MethodNodeAndOwner(mnode: MethodNode, owner: ClassNode) {
    assert(owner.methods.contains(mnode))
  }

  //--------------------------------------------------------
  // helpers to produce logging messages
  //--------------------------------------------------------

  final def methodSignature(ownerIName: String, methodName: String, methodDescriptor: String): String = {
    ownerIName + "::" + methodName + methodDescriptor
  }

  final def methodSignature(ownerBT: BType, methodName: String, methodDescriptor: String): String = {
    methodSignature(ownerBT.getInternalName, methodName, methodDescriptor)
  }

  final def methodSignature(ownerBT: BType, methodName: String, methodType: BType): String = {
    methodSignature(ownerBT.getInternalName, methodName, methodType.getDescriptor)
  }

  final def methodSignature(ownerIName: String, mnode: MethodNode): String = {
    methodSignature(ownerIName, mnode.name, mnode.desc)
  }

  final def methodSignature(ownerBT: BType, mnode: MethodNode): String = {
    methodSignature(ownerBT, mnode.name, mnode.desc)
  }

  final def methodSignature(cnode: ClassNode, mnode: MethodNode): String = {
    methodSignature(lookupRefBType(cnode.name), mnode.name, mnode.desc)
  }

  final def insnPos(insn: AbstractInsnNode, mnode: MethodNode): String = {
   s"${Util.textify(insn)} at index ${mnode.instructions.indexOf(insn)}"
  }

  final def insnPosInMethodSignature(insn: AbstractInsnNode, mnode: MethodNode, cnode: ClassNode): String = {
    insnPos(insn, mnode) + s" in method ${methodSignature(cnode, mnode)}"
  }

  final def insnPosInMethodSignature(insn: AbstractInsnNode, mnode: MethodNode, ownerIName: String): String = {
    insnPos(insn, mnode) + s" in method ${methodSignature(ownerIName, mnode)}"
  }

} // end of class BCodeOptCommon