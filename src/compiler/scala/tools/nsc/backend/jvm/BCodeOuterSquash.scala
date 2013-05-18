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
import asm.tree.analysis.SourceValue
import asm.tree._

import scala.collection.{ mutable, immutable }

/*
 *  Squash the outer pointer of Late-Closure-Classes when it's (easy to determine it's) not needed.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
abstract class BCodeOuterSquash extends BCodeSyncAndTry {

  import global._

  /*
   *  Initially all endpoints of dclosures owned by `cnode` are instance methods
   *  (unless `cnode` is an implementation-class derived from a trait,
   *  in which case all of its methods including dclosure-endpoints are static).
   *
   *  In order to invoke an instance-level endpoint, a Late-Closure-Class captures outer.
   *  However some endpoints don't actually depend on a THIS reference, ie they could be made static.
   *  A few useful facts:
   *
   *    (a) `isLiftedMethod`s and endpoints aren't part of the public type,
   *        they are implementation artifacts all whose usages can be found
   *        (for example, after turning them into static methods,
   *        their usages have to be rewritten into INVOKESTATIC)
   *
   *    (b) the "static-ness" of an endpoint containing only callsites to methods as above
   *        depends on the "static-ness" of those callees. It suffices for one of those callees
   *        not to be amenable to be made static, to preclude the endpoint from being made static.
   *
   *  Method `squashOuterForLCC()` detects the largest subset of endpoints that can be made static,
   *  under the constraint that only (a) methods can be made static, ie leaving the public API as is.
   *  Afterwards, all usages of those "must-be-made-static" methods are found, and rewritten as appropriate.
   *  The Late-Closure-Class is also modified: $outer field is removed, constructor is adapted, etc.
   *
   *  @see squashOuterForLCC()
   *
   *  @param lateClosures     dclosures owned by cnode (cnode is the "master class")
   *  @param dClosureEndpoint a map with entries (LCC-internal-name -> endpoint-as-MethodNode)
   *
   */
  final class LCCOuterSquasher(cnode: ClassNode, lateClosures: List[ClassNode], dClosureEndpoint: Map[String, MethodNode]) {

    assert(lateClosures.map(_.name).toSet == dClosureEndpoint.keySet)

    // instance methods declared by cnode are identified using a String as key, @see `key(MethodNode)`
    type KT = String

    def key(mn: MethodNode): KT = { mn.name + mn.desc }

    val masterBT = lookupRefBType(cnode.name)

    // closure name -> key of endpoint
    val epkByDCName: Map[String, KT] =
      for(
        Pair(dCName, ep) <- dClosureEndpoint;
        if Util.isInstanceMethod(ep)
      ) yield Pair(dCName, key(ep))

    // keys of all dclosure endpoints
    val isEP: Set[KT] = epkByDCName.values.toSet

    // all concrete instance methods, including <init>
    val methodsOfInterest: List[MethodNode] =
      for(mn <- cnode.toMethodList; if Util.hasBytecodeInstructions(mn) && Util.isInstanceMethod(mn))
      yield mn;

    def getKeyMethodNodeMap(ms: List[MethodNode]) = { (ms map { m => Pair(key(m), m) }).toMap }

    /*
     *  A "candidate" is a method that we might want to turn into static in order to turn an endpoint into static
     *  (and only then). Basically, to be candidate, the method must be instance and not part of the public API.
     *  This last condition is guaranteed for methods that either:
     *    (a) were originally local,  ie methods that have been lifted; or
     *    (b) are dclosure-endpoints, ie only dclosures know about them.
     *
     *  key -> MethodNode
     */
    val candidate: Map[KT, MethodNode] = {
      def canBeCandidate(mn: MethodNode): Boolean = {
        mn.isLiftedMethod && Util.isInstanceMethod(mn) && (Util.isPrivateMethod(mn) || isEP(key(mn)))
      }
      getKeyMethodNodeMap(methodsOfInterest filter canBeCandidate)
    }

    def isCandidate(s: KT) = { (s != null) && (candidate contains s) }

    /*
     *  The extractors `extractKeyLM()` and `extractKeyEP()` inform us about an usage
     *  that will require rewriting in case the "candidate" it refers to is turned into static.
     *  These extractors are used on the master class
     *  (in contrast, detecting usages in the Late-Closure-Class is the sole province of `forgetAboutOuter()`).
     *
     */

    /*
     *  Is this a callsite targeting a non-endpoint candidate (ie what used to be a Local Method)?
     *  If so, return the key for the candidate method in question, null otherwise.
     */
    def extractKeyLM(mi: MethodInsnNode): KT = {
      if (Util.isInstanceCallsite(mi) && (mi.name != "<init>") && (mi.owner == cnode.name)) {
        val s = mi.name + mi.desc
        if (isCandidate(s)) {
          return s
        }
      }
      null
    }

    /*
     *  Is this a dclosure initialization?
     *  If so, return the key for the dclosure's endpoint, null otherwise.
     */
    def extractKeyEP(mi: MethodInsnNode): KT = {
      if ((mi.getOpcode == Opcodes.INVOKESPECIAL) && (mi.name == "<init>")) {
        epkByDCName.getOrElse(mi.owner, null)
      } else null
    }

    val allCandidates: Set[KT] = candidate.keySet
    assert(isEP subsetOf allCandidates)

    def emptyKeySet = mutable.Set.empty[KT]

    /*
     *  Upong visiting the instructions of a candidate it may become clear it can't be turned into static,
     *  in which case `propagate()` "propagates" the non-staticness status up the call hierarchy.
     *  That candidate is removed from `survivors` and added to `knownCannot`.
     *
     *  Endpoints not-yet-determined-to-be-static are a subset of `survivors`
     *  yet they're also tracked in `survivingeps` for a simple reason:
     *  in case we run out of endpoints to turn into static, we can quit early.
     *
     */
    val survivors    = emptyKeySet ++ allCandidates

    val survivingeps = emptyKeySet ++ isEP

    val knownCannot  = emptyKeySet

    var toVisit: List[KT] = isEP.toList ::: (allCandidates filterNot isEP).toList

    /*
     * key of candidate C -> candidates that directly call C
     *
     * Note: methods other than candidates may contain a callsite targeting C.
     * Example:
     *
     *   def nonCandidate() {
     *
     *       def candidate(j: Int) { println(j) }
     *
     *       for(i <- 1 to 10) { candidate(i) }
     *
     *       candidate(-1)
     *
     *   }
     *
     */
    val callers = mutable.Map.empty ++ ( toVisit map { k => Pair(k, emptyKeySet) } )

    /*
     * key of candidate C -> those candidates that C contains callsites for
     */
    val callees = mutable.Map.empty ++ ( toVisit map { k => Pair(k, emptyKeySet) } )

    /*
     *  The argument has been determined must-remain-non-static.
     *  This means those methods invoking it are also precluded from being static. And so on so forth.
     */
    def propagate(k: KT) {
      knownCannot  += k
      survivingeps -= k
      survivors    -= k
      val cs = callers(k).toList
      if (cs.nonEmpty) {
        callers(k).clear
        cs foreach propagate
      }
    }

    /*
     *  Represents either THIS or an undistinguished value (which can be of JVM-level size 1 or 2)
     */
    final class TV(size: Int) extends asm.tree.analysis.Value {
      override def getSize: Int = { size }
    }

    /*
     *  A single pass is made over each candidate method, both to collect information needed later
     *  and to update maps based on the instruction just visited.
     *  This is a dataflow analysis, thus instructions can be visited multiple times.
     *  However, convergence is quite fast because of the simplistic abstract-values:
     *  one to represent THIS, and one each to represent all other values (of JVM-level size 1 or 2, respectively).
     *
     *  Upon visiting an instruction its abstract inputs are also available,
     *  which allows checking whether the method being visited can be made static:
     *
     *    (a) any consumer of THIS other than
     *        (a.1) outer-value in instantiation of a dclosure
     *        (a.2) receiver in a callsite where the callee is a candidate method
     *        results in dis-qualifying the method being visited (ie, it can't be made static),
     *        which in turn implies its direct callers can't be made static either, and so on.
     *
     *    (b) consumers as (a.1) and (a.2) above are tracked, in case at the end of the day:
     *        (b.1) they can be made static, in which case rewriting is needed to
     *              - drop the receiver, in all invocations to a non-endpoint that can be made static.
     *              - similarly for the outer value, in all instantiations of dclosures for endpoints made static.
     *        (b.2) when a consumer as in (a.1) or (a.2) can't be made static,
     *              no rewriting for those instructions is needed of course
     *              (what's needed is to propagate the non-static-ness status up the caller hierarchy,
     *              as summarized in item (a) above, but this visitor isn't responsible for that,
     *              see method `propagate()` instead).
     *
     *  All methods in this class can-multi-thread
     */
    final class ThisFlowInterpreter(current: KT) extends asm.optimiz.InterpreterSkeleton[TV] {

      import asm.tree._

      val TVTHIS = new TV(1)
      val TV1    = new TV(1)
      val TV2    = new TV(2)

      def track(v: TV) { if (v eq TVTHIS) { propagate(current) } }

      private def undet(size: Int): TV = {
        size match {
          case 1 => TV1
          case 2 => TV2
        }
      }

      override def merge(v: TV, w: TV): TV = {
        if (v == null)   return w
        if (w == null)   return v
        if (v eq TVTHIS) return TVTHIS
        if (w eq TVTHIS) return TVTHIS
        v // any of them will do
      }

      override def newValue(t: asm.Type): TV = {
        if (t == null || t == asm.Type.VOID_TYPE) { null }
        else { undet(t.getSize) }
      }

      // newOperation takes no input value, version in super is fine.

      /*
       *  this method assumes ThisFlowInterpreter is only called on instance methods.
       */
      override def copyOperation(i: AbstractInsnNode, v: TV): TV = {
        track(v)
        if (i.getOpcode == Opcodes.ALOAD) {
          val vi = i.asInstanceOf[VarInsnNode]
          if (vi.`var` == 0) {
            return TVTHIS
          }
        }
        v
      }

      override def unaryOperation(i: AbstractInsnNode, v: TV): TV = {
        track(v)
        super.unaryOperation(i, v)
      }

      override def binaryOperation(i:  AbstractInsnNode, v1: TV, v2: TV): TV = {
        track(v1)
        track(v2)
        super.binaryOperation(i, v1, v2)
      }

      override def ternaryOperation(i:  AbstractInsnNode, v1: TV, v2: TV, v3: TV): TV = {
        track(v1)
        track(v2)
        track(v3)
        null
      }

      /*
       *  Of the n-ary instructions arriving here, those that can be leveraged for outer-squashing are:
       *
       *    (a) invocation of non-endpoint candidate
       *        Note: the only invoker (before inlining) of an endpoint is an apply() method in its dclosure.
       *
       *    (b) initialization of a dclosure.
       *
       *  @param i      instruction being visited
       *  @param values comprises receiver (if any) and arguments (if any)
       */
      override def naryOperation(i:      AbstractInsnNode,
                                 values: java.util.List[_ <: TV]): TV = {
        import scala.collection.JavaConverters._
        val vs: List[TV] = values.asScala.toList
        i match {
          case mna: MultiANewArrayInsnNode => newValue(asm.Type.getType(mna.desc))
          case ivd: InvokeDynamicInsnNode  => newValue(asm.Type.getReturnType(ivd.desc))
          case mi:  MethodInsnNode =>
            if (Util.isInstanceCallsite(mi)) {
              // INVOKEVIRTUAL, INVOKESPECIAL, INVOKEINTERFACE
              trackCallsite(mi, vs)
            } else {
              vs foreach track
            }
            val rt = asm.Type.getReturnType(mi.desc)
            if (rt == asm.Type.VOID_TYPE) null // will be discarded anyway by asm.tree.analysis.Frame.execute
            else newValue(rt)
        }
      }

      private def trackCallsite(mi: MethodInsnNode, vs: List[TV]) {

        def visitCandidate(c: KT) {
          if (knownCannot(c)) propagate(current)
          else {
            callers(c)       += current
            callees(current) += c
          }
        }

        // ------ case (1 of 3) ------ initialization of dclosure
        val epk = extractKeyEP(mi)
        if (epk != null) {
          // the 2nd element in `vs` denotes outer-value, which must be TFTHIS
          assert(vs.tail.head eq TVTHIS)
          assert(vs.head      ne TVTHIS)
          vs.tail.tail foreach track
          visitCandidate(epk)
          return
        }

        // ------ case (2 of 3) ------ invocation of candidate
        val lmk = extractKeyLM(mi)
        if (lmk != null) {
          // the 1st elem in `vs` denotes the receiver, which may be (not necessarily) TVTHIS
          vs.tail foreach track
          visitCandidate(lmk)
          return
        }

        // ------ case (3 of 3) ------ a callsite to a non-candidate
        vs foreach track

      } // end of method trackCallsite()

      override def returnOperation(i: AbstractInsnNode, value: TV, expected: TV) { track(value) }

      override def drop(i: AbstractInsnNode, v: TV) { track(v) }

      override def nullValue()   = TV1
      override def intValue()    = TV1
      override def longValue()   = TV2
      override def floatValue()  = TV1
      override def doubleValue() = TV2
      override def stringValue() = TV1

      override def opAALOAD(i: InsnNode, arrayref: TV, index: TV): TV = { assert(arrayref ne TVTHIS); TV1 }

      override def opNEW(i: TypeInsnNode):       TV = { TV1 }
      override def opANEWARRAY(i: TypeInsnNode): TV = { TV1 }
      override def opCHECKCAST(i: TypeInsnNode): TV = { TV1 }

      override def opGETFIELD(fi: asm.tree.FieldInsnNode, objectref: TV): TV = {
        track(objectref)
        newValue(asm.Type.getType(fi.desc))
      }
      override def opPUTFIELD(fi: asm.tree.FieldInsnNode, objectref: TV, value: TV): TV = {
        track(objectref)
        track(value)
        value
      }

      override def opGETSTATIC(fi: FieldInsnNode):        TV = { newValue(asm.Type.getType(fi.desc)) }
      override def opPUTSTATIC(fi: FieldInsnNode, v: TV): TV = { track(v); v }

      override def opLDCHandleValue(i:     AbstractInsnNode, cst: asm.Handle): TV = { ??? }
      override def opLDCMethodTypeValue(i: AbstractInsnNode, cst: asm.Type):   TV = { ??? }

      override def opLDCRefTypeValue(i:    AbstractInsnNode, cst: asm.Type):   TV = { newValue(cst) }

    } // end of class ThisFlowInterpreter

    /*
     *  Elides redundant outer references for all dclosures that cnode is responsible for
     *  (catch: if eliding didn't happen it's because the outer-pointer wasn't redundant after all).
     *
     *  This method manages to stay brief by delegating work:
     *
     *    (a) determining candidates, setting up maps for use when ruling out candidates:
     *        delegated to the constructor of `LCCOuterSquasher`
     *    (b) ruling out candidates is delegated to `ThisFlowInterpreter` and `propagate()`
     *    (c) set of candidates that must be made static: delegated to `TransitiveClosure`
     *    (d) determining those methods containing usages of what's about to be turned into static: ok, not delegated.
     *    (e) rewriting usages in master-class: delegated to `Statifier`
     *    (f) rewriting Late-Closure-Class: delegated to `forgetAboutOuter()`
     *
     */
    def squashOuterForLCC() {

      if (lateClosures.isEmpty || isEP.isEmpty) { return }

      while (toVisit.nonEmpty) {
        val current = toVisit.head
        toVisit = toVisit.tail
        val a = new asm.tree.analysis.Analyzer[TV](new ThisFlowInterpreter(current))
        a.analyze(cnode.name, candidate(current))
        if (survivingeps.isEmpty) { return } // no dclosure will have outer removed, quit early.
      }

      // set of candidates that must be made static:
      // transitive closure over callees starting from surivivingeps
      val mustStatify: collection.Set[KT] = {
        val tc = new TransitiveClosure(callees)
        tc.walk(survivingeps)
        tc.reached
      }

      // for each method containing <init> of a dclosure whose outer was elided, those usages
      val pendingOuterElision    = (methodsOfInterest map { mn => Pair(mn, mutable.Set.empty[MethodInsnNode]) }).toMap
      val pendingReceiverElision = (methodsOfInterest map { mn => Pair(mn, mutable.Set.empty[MethodInsnNode]) }).toMap

      // methods (candidates and otherwise) containing usages of mustStatify
      val toRewrite = mutable.Set.empty[MethodNode]
      for(mn <- methodsOfInterest; k = key(mn)) {
        mn.foreachInsn {
          case mi: MethodInsnNode =>
            val call = extractKeyLM(mi)
            if ((call != null) && mustStatify(call)) {
              pendingReceiverElision(mn) += mi
              toRewrite += mn
            } else {
              val init = extractKeyEP(mi)
              if ((init != null) && mustStatify(init)) {
                pendingOuterElision(mn) += mi
                toRewrite += mn
               }
            }
          case _ => ()
        }
      }

      // rewrite usages
      for(mn <- toRewrite) {
        val pending = pendingOuterElision(mn) ++ pendingReceiverElision(mn)
        val sr = new Statifier(mn, pending)

        pendingOuterElision(mn)    foreach { init => sr elideOuter    init }
        pendingReceiverElision(mn) foreach { call => sr elideReceiver call }
        Util.computeMaxLocalsMaxStack(mn) // `dropStackElem()` does add a number of STOREs and LOADs.
      }

      // asm.optimiz.PushPopCollapser isn't used because LOAD-POP pairs cancel-out via `Statifier.dropAtSource()`

      def statify(mn: MethodNode) {
        assert(Util.isInstanceMethod(mn))
        Util.makeStaticMethod(mn)
        asm.optimiz.StaticMaker.downShiftLocalVarUsages(mn)
      }

      mustStatify foreach { k => statify(candidate(k)) }
      for(
        dcNode <- lateClosures;
        epk    <- epkByDCName.get(dcNode.name)
      ) {
        if (survivingeps(epk)) {
          forgetAboutOuter(dcNode, epk)
          log(s"Squashed outer-pointer for Late-Closure-Class ${dcNode.name}")
        } else {
          log(s"Keeping the outer-pointer for Late-Closure-Class ${dcNode.name}")
        }
      }

    } // end of method squashOuterForLCC()

    /*
     *  The division of labor between `squashOuterForLCC()` and `forgetAboutOuter()` can be explained easily:
     *    (a) `forgetAboutOuter()` rewrites a Late-Closure-Class to remove outer pointer;
     *    (b) while `squashOuterForLCC()` does all the rest, includind determining which
     *        Late-Closure-Classes should be handed to `forgetAboutOuter()`.
     */
    private def forgetAboutOuter(dcNode: ClassNode, epk: String) {

      // Step 1: outer field
      val of = dcNode.toFieldList.find(_.name == nme.OUTER.toString).get
      dcNode.fields.remove(of)

      // Step 2: first argument of <init>
      val ctor = dcNode.toMethodList.find(_.name == "<init>").get

      // Step 2.a: method descriptor of <init>
      val updatedDesc = descriptorWithoutOuter(ctor.desc)
      ctor.desc = updatedDesc

      /*
       * Step 2.b: remove PUTFIELD for $outer, ie remove:
       *    ALOAD 0
       *    ALOAD 1
       *    PUTFIELD LCC.$outer : OuterClass;
       */

      def removeFirstInstructionInCtor() {
        val h = ctor.instructions.getFirst
        ctor.instructions.remove(h)
      }

      removeFirstInstructionInCtor()
      removeFirstInstructionInCtor()
      removeFirstInstructionInCtor()

      // Step 2.c: downshift variables past local-index 1
      ctor.foreachInsn { insn =>
        if (insn.getType == AbstractInsnNode.VAR_INSN) {
          val vi = insn.asInstanceOf[VarInsnNode]
          if (vi.`var` > 1) {
            vi.`var` -= 1
          }
        }
      }

      /*
       * Step 3: one of the apply methods (the "ultimate apply") invokes the endpoint, using outer as receiver
       *    ALOAD 0
       *    GETFIELD LCC.$outer : OuterClass;
       *    . . . instructions loading arguments if any
       *    INVOKEVIRTUAL OuterClass.dlgt$....
       * Rather than finding the-one apply method containing the pattern above,
       * each apply method is explored, looking for:
       *   - GETFIELD of outer field
       *   - INVOKEVIRTUAL of endpoint
       * so as to
       *   - remove the ALOAD 0; GETFIELD outer
       *   - INVOKESTATIC
       */
      for(appMNode <- dcNode.toMethodList; if !Util.isConstructor(appMNode)) {
        val insns = appMNode.instructions.toList
        val getOuter: List[FieldInsnNode] = insns collect {
          case fi: FieldInsnNode if fi.getOpcode == Opcodes.GETFIELD && fi.name == nme.OUTER.toString => fi
        }
        assert(getOuter.isEmpty || getOuter.tail.isEmpty)
        val callEP: List[MethodInsnNode]  = insns collect {
          case mi: MethodInsnNode
            if Util.isInstanceCallsite(mi) &&
               mi.owner == cnode.name      &&
               ((mi.name + mi.desc) == epk)
          => mi
        }
        assert(callEP.isEmpty || callEP.tail.isEmpty)
        assert(getOuter.size == callEP.size)
        if (getOuter.nonEmpty) {
          val load = getOuter.head.getPrevious
          appMNode.instructions.remove(load)
          appMNode.instructions.remove(getOuter.head)

          callEP.head.setOpcode(Opcodes.INVOKESTATIC)
        }
      }

    } // end of method forgetAboutOuter()

    class TransitiveClosure[E](relation: collection.Map[E, collection.Set[E]]) {
      val reached = mutable.Set.empty[E]
      def walk(starting: Iterable[E]) {
        val direct = mutable.Set.empty[E]
        for(point <- starting; if !reached(point)) {
          reached  += point
          direct  ++= relation(point)
        }
        if (direct.nonEmpty) { walk(direct) }
      }
    }

    def toSourceValueArray(arr: Array[_ <: asm.tree.analysis.Value]): Array[SourceValue] = {
      arr map (_.asInstanceOf[SourceValue])
    }

    def descriptorWithoutOuter(desc: String): String = {
      val mt = BT.getMethodType(desc)
      val argsExceptHead = mt.getArgumentTypes.drop(1)
      val updatedDesc    = BT.getMethodDescriptor(mt.getReturnType, argsExceptHead)

      updatedDesc
    }

    class Statifier(mnode: MethodNode, pending: collection.Set[MethodInsnNode]) {

      val cp: ProdConsAnalyzer = ProdConsAnalyzer.create()
      cp.analyze(cnode.name, mnode)
      val frames: Map[AbstractInsnNode, asm.tree.analysis.Frame[_ <: asm.tree.analysis.Value]] = {
        pending map { mi => Pair(mi, cp.frameAt(mi)) }
      }.toMap

      def isSoleConsumer(producers: java.util.Set[_ <: AbstractInsnNode], consumer: AbstractInsnNode): Boolean = {
        val iter = producers.iterator()
        while (iter.hasNext) {
            val prod = iter.next
            if (!cp.hasUniqueImage(prod, consumer)) {
                return false
            }
        }
        true
      }

      def elideOuter(init: MethodInsnNode) {
        val f = frames(init)
        val actArgs = f.getActualArguments(init)
        val outerProds: SourceValue = toSourceValueArray(actArgs)(0)
        if (isSoleConsumer(outerProds.insns, init)) {
          dropAtSource(outerProds.insns)
        } else {
          // drop at sink
          val numberOfArgs = BT.getMethodType(init.desc).getArgumentCount
          dropStackElem(init, numberOfArgs - 1, 1)
        }
        val updatedDesc = descriptorWithoutOuter(init.desc)
        init.desc = updatedDesc
      }

      def elideReceiver(call: MethodInsnNode) {
        val f = frames(call)
        val rcvProds = f.getReceiver(call).asInstanceOf[SourceValue]
        if (isSoleConsumer(rcvProds.insns, call)) {
          dropAtSource(rcvProds.insns)
        } else {
          // drop at sink
          val numberOfArgs = BT.getMethodType(call.desc).getArgumentCount
          dropStackElem(call, numberOfArgs, 1)
        }
        call.setOpcode(Opcodes.INVOKESTATIC)
      }

      private def dropAtSource(producers: _root_.java.util.Set[_ <: AbstractInsnNode]) {
        val iter = producers.iterator()
        while (iter.hasNext) {
          val prod = iter.next
          if (Util.isLOAD(prod)) {
            mnode.instructions.remove(prod)
          } else {
            mnode.instructions.insert(prod, Util.getDrop(1))
          }
        }
      }

      /*
       *  Inserts STORE, POP, and LOAD, instructions so as to drop the n-th stack element counting from top starting at 0.
       *  E.g., dropStackElem(mi, 0, elemSize) amounts to dropping stack top
       *        dropStackElem(mi, 1, elemSize) drops the element pushed just before stack top, and so on.
       *
       *  As stated in analysis.Frame.getStackSize(), for the purposes of stack-indexing:
       *   "Long and double values are treated as single values."
       *
       */
      private def dropStackElem(sink: MethodInsnNode, argsToSave: Int, elemSize: Int) {
        val mt     = BT.getMethodType(sink.desc)
        val argTs  = mt.getArgumentTypes
        val stores = new InsnList
        val loads  = new InsnList
        for(n <- 0 to (argsToSave - 1)) {
          val argT  = argTs(argTs.length - 1 - n)
          val size  = argT.getSize
          val local = mnode.maxLocals
          mnode.maxLocals += size
          stores.add(  new VarInsnNode(argT.getOpcode(Opcodes.ISTORE), local))
          loads.insert(new VarInsnNode(argT.getOpcode(Opcodes.ILOAD),  local))
        }
        mnode.instructions.insertBefore(sink, stores)
        mnode.instructions.insertBefore(sink, Util.getDrop(elemSize))
        mnode.instructions.insertBefore(sink, loads)
      }

    } // end of class Statifier

  } // end of class LCCOuterSquasher

} // end of class BCodeOptIntra
