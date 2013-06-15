/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc
package backend
package jvm

import scala.tools.asm
import asm.Opcodes
import asm.optimiz.{ProdConsAnalyzer, Util}
import asm.tree._

import scala.collection.{ mutable, immutable }
import collection.convert.Wrappers.JListWrapper

/*
 *    (1) Some anonymous closures depend only on apply() arguments,
 *        ie they capture no values. In such cases, code is emitted
 *        that avoids repeated closure allocations by keeping
 *        (in a static field added to that effect) a singleton-instance
 *        that is reused.
 *
 *    (2) Lack of usages of a Late-Closure-Class (eg as a result of
 *        dead-code elimination) means the closure can be elided,
 *        along with its endpoint. This may lead to further tree-shaking
 *        (via UnusedPrivateDetector).
 *
 *    (3) Minimization of closure-fields (in particular, outer)
 *        to those actually used. Field removal requires adapting both
 *        the closure allocation site, and the Late-Closure-Class itself.
 *        For example, removing the outer-pointer also requires turning
 *        the closure's endpoint into a static method.
 *        Closure allocations remain, but with smaller GC overhead.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 *  TODO Improving the Precision and Correctness of Exception Analysis in Soot, http://www.sable.mcgill.ca/publications/techreports/#report2003-3
 *
 */
abstract class BCodeOptGCSavvyClosu extends BCodeOuterSquash {

  final class DClosureOptimizerImpl(masterCNode: ClassNode) {

    import global._

    val masterBT = lookupRefBType(masterCNode.name)
    assert(
      closuRepo.isMasterClass(masterBT),
      s"A dclosure optimmizer was instantiated for a class lacking dclosures: ${masterBT.getInternalName}"
    )

    val staticMaker = new asm.optimiz.StaticMaker

    /*
     *  (1) Find all methods declared by masterCNode fulfilling all of:
     *      private, non-constructor, non-abstract, instance, isLiftedMethod, lacking usages of THIS.
     *
     *     (Therefore, those methods that would qualify except that LOAD_0 is used for self-recursion aren't made static.
     *      This is a known limitation to keep the analysis simple).
     *
     *  (2) Make them ACC_STATIC
     *
     *  (3) scan all non-abstract methods in the class being transformed, selecting all callsites to MethodNodes found above.
     *      Adapt the instructions that provide arguments for each of those callsites, dropping the receiver.
     *
     */
    def statifyLiftedMethods() {

      var rounds = 0
      do { rounds += 1 }
      while (
        !staticMaker.transform(masterCNode).isEmpty &&
        rounds < 10
      )

    }

    /*
     * Focuses on those dclosures that the `cnode` argument is exclusively responsible for
     * (consequence: all usages of the dclosure are confined to two places: cnode and the dclosure itself).
     *
     * For each such closure, lack of usages in `cnode` (eg as a result of dead-code elimination) means
     * the closure can be elided, along with its endpoint. This may lead to further tree-shaking in `cnode` (via UnusedPrivateDetector).
     */
    def treeShakeUnusedDClosures(): Boolean = {

      val liveDCs = closuRepo.liveDClosures(masterCNode)
      if (liveDCs.isEmpty) { return false }

      val masterMethods = JListWrapper(masterCNode.methods).toList // loop body may mutate the masterCNode.methods list.

      var changed = false
      for(d <- liveDCs) {

        // if d not in use anymore (e.g., due to dead-code elimination) then remove its endpoint, and elide the class.
        val unused = {
          masterMethods forall { mnode =>
            masterCNode.methods.contains(mnode) && /* ie it hasn't been removed in a previous loop iteration */
            closuRepo.closureAccesses(mnode, d).isEmpty
          }
        }
        if (unused) {
          changed = true
          elidedClasses.add(d) // a concurrent set
          val dep = closuRepo.endpoint.get(d).mnode
          masterCNode.methods.remove(dep)
          /* At this point we should closuRepo.retractAsDClosure(d) but the supporting maps aren't concurrent,
           * and moreover all three of them should be updated atomically. Relying on elidedClasses is enough. */
        }

      }

      changed
    } // end of method treeShakeUnusedDClosures()

    /*
     *  Handle the following subcase described in minimizeDClosureAllocations():
     *
     *   (1) empty closure state: the endpoint (necessarily a static method) is invoked with (a subset of) the apply()'s arguments.
     *       In this case the closure can be turned into a singleton.
     *
     *  The `singletonize()` optimization involves adding a class-initializer
     *  (aka <clinit> , static constructor) to the Late-Closure-Class.
     *  In the Java language, "Inner classes may not declare static initializers or member interfaces." (JLS, Java 7 Edition, Sec. 8.1.3)
     *  However that's not a JVM restriction.
     *
     */
    def singletonizeDClosures() {
      for(d <- closuRepo.liveDClosures(masterCNode)) {

        val dCNode = codeRepo.classes.get(d)
        val closureState: Map[String, FieldNode] = {
          JListWrapper(dCNode.fields).toList filter { fnode => Util.isInstanceField(fnode) } map { fnode => (fnode.name -> fnode) }
        }.toMap
        val dClassDescriptor = "L" + dCNode.name + ";"

        // ------------------------------------------------------------------
        // Case (1): the dclosure can be turned into a program-wide singleton
        // ------------------------------------------------------------------
        val lacksClosureState = closureState.isEmpty
        if (lacksClosureState) {

          log(s"Singleton-closure: ${dCNode.name}")

          // -------- (1.a) modify the dclosure class (add $single static field, initialize it in <clinit>)
          val ctor = (JListWrapper(dCNode.methods) find { caller => caller.name == "<init>" }).get
          Util.makePrivateMethod(ctor)
          val single =
            new FieldNode(
              Opcodes.ASM4,
              Opcodes.ACC_PUBLIC | Opcodes.ACC_FINAL | Opcodes.ACC_STATIC,
              "$single",
              dClassDescriptor,
              null, null
            )
          dCNode.fields.add(single)
          val staticClassInitializer =
            new MethodNode(
              Opcodes.ASM4,
              Opcodes.ACC_PUBLIC | Opcodes.ACC_STATIC,
              "<clinit>",
              "()V",
              null, null
            )
          dCNode.methods.add(staticClassInitializer)
          val insns = new InsnList()
          insns.add(new TypeInsnNode(Opcodes.NEW, dCNode.name))
          insns.add(new InsnNode(Opcodes.DUP))
          insns.add(new MethodInsnNode(Opcodes.INVOKESPECIAL, dCNode.name, "<init>", "()V"))
          insns.add(new FieldInsnNode(Opcodes.PUTSTATIC, dCNode.name, single.name, dClassDescriptor))
          insns.add(new InsnNode(Opcodes.RETURN))
          staticClassInitializer.instructions.add(insns)

          // -------- (1.b) modify the master class (replace instantiation by GETSTATIC of the singleton)
          for(
            callerInMaster <- JListWrapper(masterCNode.methods);
            if Util.hasBytecodeInstructions(callerInMaster)
          ) {
            /*
             * A dclosure instantiation (the code pattern to replace) usually looks like:
             *
             *     NEW dclosure
             *     DUP
             *     INVOKESPECIAL dclosure.<init> ()V
             *
             * In a few cases it may look like:
             *
             *     NEW dclosure
             *     DUP
             *     ALOAD 0
             *     CHECKCAST X
             *     POP
             *     INVOKESPECIAL dclosure.<init> ()V
             *
             * The second case arises because PushPopCollapser doesn't back-propagate POP over CHECKCAST
             * (that would requires a type-flow based analysis).
             *
             * In both cases, the instructions of `callerInMaster` are scanned to collect two lists:
             *   (a) list of NEW dclosure
             *   (b) list of INVOKESPECIAL dclosure.<init>(...)V
             * where `dclosure` is the dclosure being singletonized.
             * Once the scan of `callerInMaster.instructions` is over,
             *   (c) elements of (a) and their following DUP are removed,
             *   (d) elements of (b) are turned into GETSTATIC singleton
             *
             */

            var newInsns: List[AbstractInsnNode] = Nil
            var iniInsns: List[AbstractInsnNode] = Nil

            callerInMaster.foreachInsn { insn =>
              if (insn.getOpcode == Opcodes.NEW) {
                val ti = insn.asInstanceOf[TypeInsnNode]
                if (ti.desc == dCNode.name) {
                  newInsns ::= ti
                }
              } else if (insn.getOpcode == Opcodes.INVOKESPECIAL) {
                val mi = insn.asInstanceOf[MethodInsnNode]
                if ((mi.name == "<init>") && (mi.owner == dCNode.name)) {
                  iniInsns ::= mi
                }
              }
            }

            val stream = callerInMaster.instructions
            for(ni <- newInsns) {
              val dup = ni.getNext
              assert(dup.getOpcode == Opcodes.DUP)
              stream.remove(ni)
              stream.remove(dup)
            }
            for(ini <- iniInsns) {
              stream.set(
                ini,
                new FieldInsnNode(Opcodes.GETSTATIC, dCNode.name, single.name, single.desc)
              )
            }

          }

        }

      }

    } // end of method singletonizeDClosures()

  } // end of class DClosureOptimizerImpl

} // end of class BCodeOptGCSavvyClosu
