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
     * Focuses on those dclosures that the `cnode` argument is exclusively responsible for
     * (consequence: all usages of the dclosure are confined to two places: cnode and the dclosure itself).
     *
     * For each such closure:
     *
     *   (1) lack of usages in `cnode` (eg as a result of dead-code elimination) means the closure can be elided,
     *       along with its endpoint. This may lead to further tree-shaking in `cnode` (via UnusedPrivateDetector).
     *
     *   (2) minimize the dclosure fields (in particular, outer) to those actually used.
     *       "Minimizing the outer instance" means the endpoint is made static.
     *       The dclosure itself remains, but with smaller GC overhead.
     *
     * This method can be run on the ClassNode of a Serializable class:
     * only isLiftedMethods or dclosure-endpoints will be mutated.
     *
     */
    def minimizeDClosureFields(): Boolean = {

      var rounds = 0
      do { rounds += 1 }
      while (
        !staticMaker.transform(masterCNode).isEmpty &&
        rounds < 10
      )

      var changed = false
      for(d <- closuRepo.liveDClosures(masterCNode)) {

        val dep = closuRepo.endpoint.get(d).mnode
        // the dclosure remains in use in cnode (it wasn't elided). The endpoint must still be there.
        assert(masterCNode.methods.contains(dep))
        assert(Util.isPublicMethod(dep))
        changed |= minimizeDClosureFields(dep, d)

      }

      changed
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
     * All usages of the dclosure are confined to two places: its master class and the dclosure itself.
     * We can minimize dclosure fields (in particular, outer) because we know where to find
     * all of the (dclosure instantiations, endpoint invocations) that will require adapting to remain well-formed.
     *
     */
    private def minimizeDClosureFields(endpoint: MethodNode, d: BType): Boolean = {
      import asm.optimiz.UnusedParamsElider
      import asm.optimiz.StaticMaker

      assertPipeline1Done(
        "This optimization might register a yet unseen method descriptor. Before doing so, global is locked." +
        "For that to work, pipeline-1 must have completed (because Worker1 registers itselfs new BTypes, without locking)."
      )

      val dCNode: ClassNode = codeRepo.classes.get(d)

      /*
       *  (1) remove params that go unused at the endpoint in the master class,
       *      also removing the arguments provided by the callsite in the dclosure class.
       *
       *  (2) attempt to make static the endpoint (and its invocation).
       *
       *  A master-class of a non-elided dclosure contains:
       *    - one or more instantiations of it (may be more than one because of duplication of catch and try clauses), and
       *    - no invocations to the dclosure's endpoint
       *     (the "non-elided" part is responsible for "no invocations to the dclosure's endpoint":
       *      a dclosure that was inlined has a callsite to the endpoint in the shio method
       *      that replaces the higher-order method invocation).
       *
       */
      def adaptEndpointAndItsCallsite(): Boolean = {
        var changed  = false
        val oldDescr = endpoint.desc
        // don't run UnusedPrivateDetector on a ClassNode with a method temporarily made private.
        Util.makePrivateMethod(endpoint) // temporarily

        val elidedParams: java.util.Set[java.lang.Integer] = UnusedParamsElider.elideUnusedParams(masterCNode, endpoint)
        if (!elidedParams.isEmpty) {
          changed = true
          global synchronized {
            BT.getMethodType(endpoint.desc)
          }
          log(
           s"In order to minimize closure-fields, one or more params were elided from endpoint ${methodSignature(masterCNode, endpoint)} " +
           s". Before the change, its method descriptor was $oldDescr"
          )
          for(dmethod <- JListWrapper(dCNode.methods)) {
            UnusedParamsElider.elideArguments(dCNode, dmethod, masterCNode, endpoint, oldDescr, elidedParams)
          }
          closuRepo.assertEndpointInvocationsIsEmpty(masterCNode, d) /*debug*/
        }

        if (Util.isInstanceMethod(endpoint) && StaticMaker.lacksUsagesOfTHIS(endpoint)) {
          changed = true
          log(s"In order to minimize closure-fields, made static endpoint ${methodSignature(masterCNode, endpoint)}")
          Util.makeStaticMethod(endpoint)
          StaticMaker.downShiftLocalVarUsages(endpoint)
          for (dmethod <- JListWrapper(dCNode.methods)) {
            assert(!Util.isAbstractMethod(dmethod))
            StaticMaker.adaptCallsitesTargeting(dCNode, dmethod, masterCNode, endpoint)
          }
          closuRepo.assertEndpointInvocationsIsEmpty(masterCNode, d) /*debug*/
        }

        Util.makePublicMethod(endpoint)

        changed
      }

      if (!adaptEndpointAndItsCallsite()) {
        return false
      }

      // past this point one or more closure-fields are to be elided (outer instance, captured local, or any combination thereof).

      // PUTFIELD instructions for dclosure-fields that are never read can be eliminated,
      // which in turn is a pre-requisite for removal of redundant closure-state fields.
      // The whole process involves several steps.

      /*
       * Step 1: cancel-out DROP of closure-state GETFIELD
       * -------------------------------------------------
       *
       * Even if PushPopCollapser is run on the dclosure, instruction pairs of the form:
       *   LOAD_0
       *   GETFIELD of a closure-field
       *   DROP
       * still remain (PushPopCollapser does not elide a GETFIELD of a private final field,
       * because it doesn't check whether it's been assigned already or not).
       *
       * The custom transform below gets rid of those GETFIELD instructions, rewriting the above into:
       *   LOAD_0
       *   DROP
       *
       * A follow-up round of PushPopCollapser finishes the code clean-up.
       */
      val cp = ProdConsAnalyzer.create()
      for (caller <- JListWrapper(dCNode.methods)) {
        Util.computeMaxLocalsMaxStack(caller)
        cp.analyze(dCNode.name, caller)
        for(
          // we'll modify caller.instructions in the for-body, that's fine because toList returns another list.
          drop <- caller.instructions.toList;
          if Util.isDROP(drop);
          producers = cp.producers(drop);
          if producers.size() == 1;
          prod = producers.iterator().next;
          if prod.getOpcode == Opcodes.GETFIELD;
          if prod.asInstanceOf[FieldInsnNode].owner == dCNode.name;
          if cp.isPointToPoint(prod, drop)
        ) {
          caller.instructions.set(prod, Util.getDrop(1)) // drop the receiver of GETFIELD, ie drop the result of LOAD_0
          caller.instructions.remove(drop)               // cancel-out the DROP for the result of GETFIELD
        }
      }

      val cleanser = createBCodeCleanser(dCNode, isIntraProgramOpt = false)
      cleanser.intraMethodFixpoints(full = false)

      /*
       * Step 2: determine (declared) `closureState` and (effectively used) `whatGetsRead`
       * ---------------------------------------------------------------------------------
       */
      val closureState: Map[String, FieldNode] = {
        JListWrapper(dCNode.fields).toList filter { fnode => Util.isInstanceField(fnode) } map { fnode => (fnode.name -> fnode) }
      }.toMap
      val whatGetsRead = mutable.Set.empty[String]
      for(
        caller <- JListWrapper(dCNode.methods);
        insn   <- caller.instructions.toList
      ) {
        if (insn.getOpcode == Opcodes.GETFIELD) {
          val fieldRead = insn.asInstanceOf[FieldInsnNode]
          assert(fieldRead.owner == dCNode.name)
          if (closureState.contains(fieldRead.name)) {
            whatGetsRead += fieldRead.name
          }
        }
      }

      if (whatGetsRead.size == closureState.size) {
        // elidedParams may refer to an apply-arg or a captured local, or combination thereof.
        return true // no closure-state field to elide after all (e.g., outer was a module, see test/files/run/Course-2002-10.scala)
      }

      val fieldsToRemove = for(Pair(fname, fnode) <- closureState; if !whatGetsRead.contains(fname) ) yield fnode;
      log(
       s"Minimizing closure-fields in dclosure ${d.getInternalName}. The following fields will be removed " +
       (fieldsToRemove map { fnode => fnode.name + " : " + fnode.desc }).mkString
      )

      /*
       * Step 3: determine correspondence redundant-closure-field-name -> constructor-params-position
       * --------------------------------------------------------------------------------------------
       */
      // redundant-closure-field-name -> zero-based position the constructor param providing the value for it.
      val posOfRedundantCtorParam = mutable.Map.empty[String, Int]
      val ctor = (JListWrapper(dCNode.methods) find { caller => caller.name == "<init>" }).get
      val ctorBT = BT.getMethodType(ctor.desc)
      Util.computeMaxLocalsMaxStack(ctor)
      cp.analyze(dCNode.name, ctor)
      for(
        insn   <- ctor.instructions.toList
      ) {
        if (insn.getOpcode == Opcodes.PUTFIELD) {
          val fieldWrite = insn.asInstanceOf[FieldInsnNode]
          assert(fieldWrite.owner == dCNode.name)
          if (!whatGetsRead.contains(fieldWrite.name)) {
            import collection.convert.Wrappers.JSetWrapper
            val nonThisLocals = {
              JSetWrapper(cp.producers(fieldWrite)) map { insn => insn.asInstanceOf[VarInsnNode].`var` } filterNot { _ == 0 }
            }
            assert(nonThisLocals.size == 1)
            assert(!posOfRedundantCtorParam.contains(fieldWrite.name))
            val localVarIdx = nonThisLocals.iterator.next
            val paramPos    = ctorBT.convertLocalVarIdxToFormalParamPos(localVarIdx, true)
            posOfRedundantCtorParam.put(fieldWrite.name, paramPos)
          }
        }
      }
      assert(posOfRedundantCtorParam.nonEmpty)

      val isOuterRedundant = {
         closureState.contains(nme.OUTER.toString) &&
        !whatGetsRead.contains(nme.OUTER.toString)
      }

      /*
       * Step 4: in the dclosure (e.g. its constructor) get rid of PUTFIELDs to closure-state fields never read
       * ------------------------------------------------------------------------------------------------------
       */
      for(
        caller <- JListWrapper(dCNode.methods);
        insn   <- caller.instructions.toList
      ) {
        if (insn.getOpcode == Opcodes.PUTFIELD) {
          val fieldWrite = insn.asInstanceOf[FieldInsnNode]
          assert(fieldWrite.owner == dCNode.name)
          if (!whatGetsRead.contains(fieldWrite.name)) {
            val fnode = closureState(fieldWrite.name)
            val size  = descrToBType(fnode.desc).getSize
            caller.instructions.insert(fieldWrite, Util.getDrop(1)) // drops THIS
            caller.instructions.set(fieldWrite, Util.getDrop(size)) // drops field value
          }
        }
      }

      /*
       * Step 5: back-propagate DROPs inserted above, and remove redundant fields
       * (otherwise another attempt will be made to delete them next time around)
       * ------------------------------------------------------------------------
       */
      cleanser.intraMethodFixpoints(full = false)
      for(fnode <- closureState.values; if !whatGetsRead.contains(fnode.name)) {
        dCNode.fields.remove(fnode)
      }

      /*
       * Step 6: adapt the method descriptor of the dclosure constructor, as well as <init> callsite in master class
       * -----------------------------------------------------------------------------------------------------------
       */
      Util.makePrivateMethod(ctor) // temporarily
      val oldCtorDescr = ctor.desc
      val elideCtorParams: java.util.Set[java.lang.Integer] = UnusedParamsElider.elideUnusedParams(dCNode, ctor)
      Util.makePublicMethod(ctor)
      global synchronized {
        BT.getMethodType(ctor.desc)
      }
      assert(!elideCtorParams.isEmpty)
      for(callerInMaster <- JListWrapper(masterCNode.methods)) {
        UnusedParamsElider.elideArguments(masterCNode, callerInMaster, dCNode, ctor, oldCtorDescr, elideCtorParams)
      }

      true
    } // end of method minimizeDClosureFields()

    /*
     * Once no further `minimizeDClosureFields()` is possible, dclosures can be partitioned into the following classes:
     *
     *   (1) empty closure state: the endpoint (necessarily a static method) is invoked with (a subset of) the apply()'s arguments.
     *       In this case the closure can be turned into a singleton.
     *
     *   (2) closure state consisting only of outer-instance: irrespective of the dclosure's arity,
     *       besides (a subset of) the apply()'s arguments, the only additional value needed
     *       to invoke the endpoint is the outer-instance value.
     *       In this case the closure can be allocated once per outer-instance
     *       (for example, in the constructor of the class of the outer instance).
     *       "Per-outer-instance closure-singletons" are a trade-off: the assumption being their instantiation
     *       will be amortized over the many times it's passed as argument.
     *
     *   (3) closure state consists of one or more values other than the outer instance, if any.
     *
     *       In other words the subcases are:
     *         (3.a) the outer-instance and one or more captured values, or
     *         (3.b) one or more captured values,
     *       constitute the closure state.
     *       Under (3.a) the endpoint is an instance-method, while for (3.b) it's static.
     *
     *       In this last case (3), an allocation is needed each time the closure is passed as argument (to convey those captured values).
     *
     *       In theory two closures of the same closure-class capturing the same values are inter-changeable,
     *       thus a runtime "dictionary lookup" could provide an existing closure instance for a given tuple of captured values. Expensive.
     *
     */
    def minimizeDClosureAllocations() {
      singletonizeDClosures()         // Case (1) empty closure state
    }

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
    private def singletonizeDClosures() {
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
