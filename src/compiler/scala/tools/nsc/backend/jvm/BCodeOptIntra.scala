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
import collection.convert.Wrappers.JListWrapper
import collection.convert.Wrappers.JSetWrapper

/**
 *  Optimize and tidy-up bytecode before it's serialized for good.
 *  This class focuses on
 *    - intra-method optimizations,
 *    - intra-class  optimizations, and
 *    - utilities for the above and for inter-procedural optimizations as well.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 *  TODO Improving the Precision and Correctness of Exception Analysis in Soot, http://www.sable.mcgill.ca/publications/techreports/#report2003-3
 *
 */
abstract class BCodeOptIntra extends BCodeOptCommon {

  import global._

  final override def createBCodeCleanser(cnode: asm.tree.ClassNode, isInterClosureOptimizOn: Boolean) = {
    new BCodeCleanser(cnode, isInterClosureOptimizOn)
  }

  final override def createQuickCleanser(cnode: asm.tree.ClassNode) = {
    new QuickCleanser(cnode)
  }

  val knownLacksInline = mutable.Set.empty[Symbol] // cache to avoid multiple inliner.hasInline() calls.
  val knownHasInline   = mutable.Set.empty[Symbol] // as above. Motivated by the need to warn on "inliner failures".

  final def hasInline(sym: Symbol) = {
    if     (knownLacksInline(sym)) false
    else if(knownHasInline(sym))   true
    else {
      val b = (sym hasAnnotation definitions.ScalaInlineClass)
      if(b) { knownHasInline   += sym }
      else  { knownLacksInline += sym }

      b
    }
  }

  final def hasNoInline(sym: Symbol) = sym hasAnnotation definitions.ScalaNoInlineClass

  /**
   * must-single-thread
   **/
  def clearBCodeOpt() {
    knownLacksInline.clear()
    knownHasInline.clear()
  }

  /**
   *  SI-6720: Avoid java.lang.VerifyError: Uninitialized object exists on backward branch.
   *
   *  Quoting from the JVM Spec, 4.9.2 Structural Constraints , http://docs.oracle.com/javase/specs/jvms/se7/html/jvms-4.html
   *
   *     There must never be an uninitialized class instance on the operand stack or in a local variable
   *     at the target of a backwards branch unless the special type of the uninitialized class instance
   *     at the branch instruction is merged with itself at the target of the branch (Sec. 4.10.2.4).
   *
   *  The Oracle JVM as of JDK 7 has started rejecting bytecode of the form:
   *
   *      NEW x
   *      DUP
   *      ... instructions loading ctor-args, involving a backedge
   *      INVOKESPECIAL <init>
   *
   *  `rephraseBackedgesInConstructorArgs()` overcomes the above by reformulating into:
   *
   *      ... instructions loading ctor-arg N
   *      STORE nth-arg
   *      ... instructions loading ctor-arg (N-1)
   *      STORE (n-1)th-arg
   *      ... and so on
   *      STORE 1st-arg
   *      NEW x
   *      DUP
   *      LOAD 1st-arg
   *      ...
   *      LOAD nth-arg
   *      INVOKESPECIAL <init>
   *
   *  A warning informs that, in the rewritten version, `NEW x` comes after the code to compute arguments.
   *  It's either that (potential) behavioral change or VerifyError.
   *  "Behavioral change" that is, in case the class being instantiated has a side-effecting static initializer.
   *
   *  @param nxtIdx0  next available index for local variable
   *  @param bes      backedges in ctor-arg section
   *  @param newInsn  left  bracket of the section where backedges were found
   *  @param initInsn right bracket of the section where backedges were found
   *
   * */
  def rephraseBackedgesInCtorArg(nxtIdx0:  Int,
                                 bes:      _root_.java.util.Map[asm.tree.JumpInsnNode, asm.tree.LabelNode],
                                 cnode:    asm.tree.ClassNode,
                                 mnode:    asm.tree.MethodNode,
                                 newInsn:  asm.tree.TypeInsnNode,
                                 initInsn: MethodInsnNode): Int = {

    var nxtIdx = nxtIdx0

    import collection.convert.Wrappers.JSetWrapper
    for(
      entry <- JSetWrapper(bes.entrySet());
      jump  = entry.getKey;
      label = entry.getValue
    ) {
      warning(
        s"Backedge found in contructor-args section, in method ${methodSignature(cnode, mnode)} " +
        s"(jump ${insnPos(jump, mnode)} , target ${insnPos(label, mnode)} ). " +
        s"In order to avoid SI-6720, adding LOADs and STOREs for arguments. "  +
        s"As a result, ${newInsn.desc} is now instantiated after evaluating all ctor-arguments, " +
        s"on the assumption such class has not static-ctor performing visible side-effects that could make a difference."
      )
    }

    assert(newInsn.getOpcode == asm.Opcodes.NEW)
    val dupInsn = newInsn.getNext
    val paramTypes = BType.getMethodType(initInsn.desc).getArgumentTypes

    val stream = mnode.instructions
    stream.remove(newInsn)
    stream.remove(dupInsn)
    stream.insertBefore(initInsn, newInsn)
    stream.insertBefore(initInsn, dupInsn)

    for(i <- (paramTypes.length - 1) to 0 by -1) {
      val pt = paramTypes(i)
      val idxVar = nxtIdx
      nxtIdx += pt.getSize
      val load  = new asm.tree.VarInsnNode(pt.getOpcode(asm.Opcodes.ILOAD),  idxVar)
      val store = new asm.tree.VarInsnNode(pt.getOpcode(asm.Opcodes.ISTORE), idxVar)
      stream.insertBefore(newInsn, store)
      stream.insert(dupInsn,load)
    }

    nxtIdx
  } // end of method rephraseBackedgesInCtorArg()

  /**
   *  All methods in this class can-multi-thread
   */
  class EssentialCleanser(cnode: asm.tree.ClassNode) {

    val jumpsCollapser      = new asm.optimiz.JumpChainsCollapser()
    val labelsCleanup       = new asm.optimiz.LabelsCleanup()
    val danglingExcHandlers = new asm.optimiz.DanglingExcHandlers()

    /**
     *  This method performs a few intra-method optimizations:
     *    - collapse a multi-jump chain to target its final destination via a single jump
     *    - remove unreachable code
     *    - remove those LabelNodes and LineNumbers that aren't in use
     *
     *  Some of the above are applied repeatedly until no further reductions occur.
     *
     *  Node: what ICode calls reaching-defs is available as asm.tree.analysis.SourceInterpreter, but isn't used here.
     *
     */
    final def cleanseMethod(cName: String, mnode: asm.tree.MethodNode): Boolean = {

      var changed = false
      var keepGoing = false

      do {
        keepGoing = false

        jumpsCollapser.transform(mnode)            // collapse a multi-jump chain to target its final destination via a single jump
        keepGoing |= jumpsCollapser.changed

        keepGoing |= removeUnreachableCode(mnode)

        labelsCleanup.transform(mnode)             // remove those LabelNodes and LineNumbers that aren't in use
        keepGoing |= labelsCleanup.changed

        danglingExcHandlers.transform(mnode)
        keepGoing |= danglingExcHandlers.changed

        changed |= keepGoing

      } while (keepGoing)

      ifDebug { repOK(mnode) }

      changed

    }

    /**
     * Detects and removes unreachable code.
     *
     * Should be used last in a transformation chain, before stack map frames are computed.
     * The Java 6 verifier demands frames be available even for dead code.
     * Those frames are tricky to compute, http://asm.ow2.org/doc/developer-guide.html#deadcode
     * The problem is avoided altogether by not emitting unreachable code in the first place.
     *
     * This method has a lower memory footprint than `asm.optimiz.UnreachableCode`
     * Otherwise both versions accomplish the same.
     *
     */
    final def removeUnreachableCode(mnode: MethodNode): Boolean = {

      val landing  = mutable.Set.empty[AbstractInsnNode]
      val suspect  = mutable.Set.empty[AbstractInsnNode]
      val worklist = new mutable.Stack[AbstractInsnNode]

          def transfer(to: AbstractInsnNode) {
            if(to == null)  { return }
            suspect -= to
            if(landing(to)) { return }
            landing += to
            if(to.getType == AbstractInsnNode.LABEL) { transfer(to.getNext) }
            else {
              worklist push to
            }
          }

          def transfers(labels: _root_.java.util.List[LabelNode]) {
            for(lbl <- JListWrapper(labels)) { transfer(lbl) }
          }

          def makeSuspect(s: AbstractInsnNode) {
            if(s == null) { return }
            if(!landing(s)) {
              suspect += s
             }
          }

      val stream = mnode.instructions
      transfer(stream.getFirst)
      for(tcb <- JListWrapper(mnode.tryCatchBlocks)) { transfer(tcb.handler) }

      while(worklist.nonEmpty) {
        var reach = worklist.pop()
        while(reach != null) {

          reach.getType match {
            case AbstractInsnNode.LABEL =>
              transfer(reach)
              reach = null
            case AbstractInsnNode.JUMP_INSN =>
              val ji = reach.asInstanceOf[JumpInsnNode]
              if(ji.getOpcode == Opcodes.JSR) {
                return false // don't touch methods containing subroutines (perhaps was inlined, scalac doesn't emit JSR/RET)
              }
              if(Util.isCondJump(reach)) {
                transfer(ji.label)
                transfer(reach.getNext)
              } else {
                assert(reach.getOpcode == Opcodes.GOTO)
                transfer(ji.label)
                makeSuspect(reach.getNext)
              }
              reach = null
            case AbstractInsnNode.LOOKUPSWITCH_INSN =>
              val lsi = reach.asInstanceOf[LookupSwitchInsnNode]
              transfer(lsi.dflt)
              transfers(lsi.labels)
              reach = null
            case AbstractInsnNode.TABLESWITCH_INSN =>
              val tsi = reach.asInstanceOf[TableSwitchInsnNode]
              transfer(tsi.dflt)
              transfers(tsi.labels)
              reach = null
            case AbstractInsnNode.INSN =>
              val isATHROW = (reach.getOpcode == Opcodes.ATHROW)
              if(isATHROW || Util.isRETURN(reach)) {
                makeSuspect(reach.getNext)
                reach = null
              }
            case _ =>
              if(reach.getOpcode == Opcodes.RET) {
                return false // don't touch methods containing subroutines (perhaps was inlined, scalac doesn't emit JSR/RET)
              }
              ()
          }

          if(reach != null) {
            reach = reach.getNext
          }

        }
      }

      // pruning
      var changed = false
      for(s <- suspect) {
        var current = s
        while(current != null && !landing(current) && stream.contains(current)) {
          val nxt = current.getNext
          if(current.getType != AbstractInsnNode.LABEL) { // let asm.optimiz.LabelsCleanup take care of LabelNodes
            changed = true
            stream remove current
          }
          current = nxt
        }
      }

      changed
    }

    /**
     *  (1) Removes dead code, and (2) elide redundant outer-fields for Late-Closure-Classes.
     *
     *  When writing classfiles with "optimization level zero" (ie -neo:GenBCode)
     *  the very least we want to do is remove dead code beforehand,
     *  so as to prevent an artifact of stack-frames computation from showing up,
     *  the artifact described at http://asm.ow2.org/doc/developer-guide.html#deadcode
     *  That artifact results from the requirement by the Java 6 split verifier
     *  that a stack map frame be available for each basic block, even unreachable ones.
     *
     *  Just removing dead code might leave stale LocalVariableTable entries
     *  thus `cleanseMethod()` also gets rid of those.
     *
     * */
    final def codeFixups(lateClosures: List[ClassNode]) {
      // 1 of 2
      val iter = cnode.methods.iterator()
      while(iter.hasNext) {
        val mnode = iter.next()
        if(Util.hasBytecodeInstructions(mnode)) {
          Util.computeMaxLocalsMaxStack(mnode)
          cleanseMethod(cnode.name, mnode) // remove unreachable code
        }
      }
      // 2 of 2
      if(!cnode.isStaticModule && lateClosures.nonEmpty) {
        val sq = new LCCOuterSquasher
        sq.squashOuterForLCC(lateClosures)
      }
    }

    /**
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
     * */
    final class LCCOuterSquasher {

      // instance methods declared by cnode are identified using a String as key, @see `key(MethodNode)`
      type KT = String

      def key(mn: MethodNode): KT = { mn.name + mn.desc }

      val masterBT = lookupRefBType(cnode.name)

      // dclosures owned by cnode (cnode is the "master class")
      val dcbts: List[BType] = {
        val dcbts0 = closuRepo.dclosures.get(masterBT)
        if(dcbts0 == null) Nil else dcbts0
      }

      // closure name -> key of endpoint
      val epByDCName: Map[String, KT] = (
        for(
          closuBT <- dcbts;
          ep = closuRepo.endpoint.get(closuBT).mnode;
          if Util.isInstanceMethod(ep)
        ) yield Pair(closuBT.getInternalName, key(ep))
      ).toMap

      // keys of all dclosure endpoints
      val isEP: Set[KT] = epByDCName.values.toSet

      // all concrete instance methods, including <init>
      val methodsOfInterest: List[MethodNode] =
        for(mn <- cnode.toMethodList; if Util.hasBytecodeInstructions(mn) && Util.isInstanceMethod(mn))
        yield mn;

          def getKeyMethodNodeMap(ms: List[MethodNode]) = { (ms map { m => Pair(key(m), m) }).toMap }

      /**
       *  A "candidate" is a method that we might want to turn into static in order to turn an endpoint into static
       *  (and only then). Basically, to be candidate, the method must be instance and not part of the public API.
       *  This last condition is guaranteed for methods that either:
       *    (a) were originally local,  ie methods that have been lifted; or
       *    (b) are dclosure-endpoints, ie only dclosures know about them.
       *
       *  key -> MethodNode
       * */
      val candidate: Map[KT, MethodNode] = {
        def canBeCandidate(mn: MethodNode): Boolean = {
          mn.isLiftedMethod && Util.isInstanceMethod(mn) && (Util.isPrivateMethod(mn) || isEP(key(mn)))
        }
        getKeyMethodNodeMap(methodsOfInterest filter canBeCandidate)
      }

      def isCandidate(s: KT) = { (s != null) && (candidate contains s) }

      /**
       *  The extractors `extractKeyLM()` and `extractKeyEP()` inform us about an usage
       *  that will require rewriting in case the "candidate" it refers to is turned into static.
       *  These extractors are used on the master class
       *  (in contrast, detecting usages in the Late-Closure-Class is the sole province of `forgetAboutOuter()`).
       *
       * */

      /**
       *  Is this a callsite targeting a non-endpoint candidate (ie what used to be a Local Method)?
       *  If so, return the key for the candidate method in question, null otherwise.
       * */
      def extractKeyLM(mi: MethodInsnNode): KT = {
        if(Util.isInstanceCallsite(mi) && (mi.name != "<init>") && (mi.owner == cnode.name)) {
            val s = mi.name + mi.desc
            if(isCandidate(s)) {
              return s
            }
        }
        null
      }

      /**
       *  Is this a dclosure initialization?
       *  If so, return the key for the dclosure's endpoint, null otherwise.
       * */
      def extractKeyEP(mi: MethodInsnNode): KT = {
        if((mi.getOpcode == Opcodes.INVOKESPECIAL) && (mi.name == "<init>")) {
            epByDCName.getOrElse(mi.owner, null)
        } else null
      }

      val allCandidates: Set[KT] = candidate.keySet
      assert(isEP subsetOf allCandidates)

          def emptyKeySet = mutable.Set.empty[KT]

      /**
       *  Upong visiting the instructions of a candidate it may become clear it can't be turned into static,
       *  in which case `propagate()` "propagates" the non-staticness status up the call hierarchy.
       *  That candidate is removed from `survivors` and added to `knownCannot`.
       *
       *  Endpoints not-yet-determined-to-be-static are a subset of `survivors`
       *  yet they're also tracked in `survivingeps` for a simple reason:
       *  in case we run out of endpoints to turn into static, we can quit early.
       *
       * */
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

        /**
         *  The argument has been determined must-remain-non-static.
         *  This means those methods invoking it are also precluded from being static. And so on so forth.
         * */
        def propagate(k: KT) {
          knownCannot  += k
          survivingeps -= k
          survivors    -= k
          val cs = callers(k).toList
          if(cs.nonEmpty) {
            callers(k).clear
            cs foreach propagate
          }
        }

        /**
         *  Represents either THIS or an undistinguished value (which can be of JVM-level size 1 or 2)
         */
        final class TV(size: Int) extends asm.tree.analysis.Value {
          override def getSize: Int = { size }
        }

        /**
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
         **/
        final class ThisFlowInterpreter(current: KT) extends asm.optimiz.InterpreterSkeleton[TV] {

          import asm.tree._

          val TVTHIS = new TV(1)
          val TV1    = new TV(1)
          val TV2    = new TV(2)

          def track(v: TV) { if(v eq TVTHIS) { propagate(current) } }

          private def undet(size: Int): TV = {
            size match {
              case 1 => TV1
              case 2 => TV2
            }
          }

          override def merge(v: TV, w: TV): TV = {
            if(v == null)   return w
            if(w == null)   return v
            if(v eq TVTHIS) return TVTHIS
            if(w eq TVTHIS) return TVTHIS
            v // any of them will do
          }

          override def newValue(t: asm.Type): TV = {
            if (t == null || t == asm.Type.VOID_TYPE) { null }
            else { undet(t.getSize) }
          }

          // newOperation takes no input value, version in super is fine.

          /**
           *  this method assumes ThisFlowInterpreter is only called on instance methods.
           * */
          override def copyOperation(i: AbstractInsnNode, v: TV): TV = {
            track(v)
            if(i.getOpcode == Opcodes.ALOAD) {
              val vi = i.asInstanceOf[VarInsnNode]
              if(vi.`var` == 0) {
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

          /**
           *  Of the n-ary instructions arriving here, those that can be leveraged for outer-squashing are:
           *
           *    (a) invocation of non-endpoint candidate
           *        Note: the only invoker (before inlining) of an endpoint is an apply() method in its dclosure.
           *
           *    (b) initialization of a dclosure.
           *
           *  @param i      instruction being visited
           *  @param values comprises receiver (if any) and arguments (if any)
           * */
          override def naryOperation(i:      AbstractInsnNode,
                                     values: java.util.List[_ <: TV]): TV = {
            val vs = JListWrapper(values).toList
            i match {
              case mna: MultiANewArrayInsnNode => newValue(asm.Type.getType(mna.desc))
              case ivd: InvokeDynamicInsnNode  => newValue(asm.Type.getReturnType(ivd.desc))
              case mi:  MethodInsnNode =>
                if(Util.isInstanceCallsite(mi)) {
                  // INVOKEVIRTUAL, INVOKESPECIAL, INVOKEINTERFACE
                  trackCallsite(mi, vs)
                } else {
                  vs foreach track
                }
                val rt = asm.Type.getReturnType(mi.desc)
                if(rt == asm.Type.VOID_TYPE) null // will be discarded anyway by asm.tree.analysis.Frame.execute
                else newValue(rt)
            }
          }

          private def trackCallsite(mi: MethodInsnNode, vs: List[TV]) {

                def visitCandidate(c: KT) {
                  if(knownCannot(c)) propagate(current)
                  else {
                    callers(c)       += current
                    callees(current) += c
                  }
                }

            // ------ case (1 of 3) ------ initialization of dclosure
            val epk = extractKeyEP(mi)
            if(epk != null) {
              // the 2nd element in `vs` denotes outer-value, which must be TFTHIS
              assert(vs.tail.head eq TVTHIS)
              assert(vs.head      ne TVTHIS)
              vs.tail.tail foreach track
              visitCandidate(epk)
              return
            }

            // ------ case (2 of 3) ------ invocation of candidate
            val lmk = extractKeyLM(mi)
            if(lmk != null) {
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

      /**
       *  Elides redundant outer references for all dclosures that cnode is responsible for
       *  (catch: if eliding didn't happen is because the outer-pointer wasn't redundant after all).
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
       * */
      def squashOuterForLCC(lateClosures: List[ClassNode]) {

        if(dcbts.isEmpty || isEP.isEmpty) { return }

        while(toVisit.nonEmpty) {
          val current = toVisit.head
          toVisit = toVisit.tail
          val a = new asm.tree.analysis.Analyzer[TV](new ThisFlowInterpreter(current))
          a.analyze(cnode.name, candidate(current))
          if(survivingeps.isEmpty) { return } // no dclosure will have outer removed, quit early.
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
              if((call != null) && mustStatify(call)) {
                pendingReceiverElision(mn) += mi
                toRewrite += mn
              } else {
                val init = extractKeyEP(mi)
                if((init != null) && mustStatify(init)) {
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
          epk = epByDCName.getOrElse(dcNode.name, null);
          if (epk != null)
        ) {
          if(survivingeps(epk)) {
            forgetAboutOuter(dcNode, epk)
            log(s"Squashed outer-pointer for Late-Closure-Class ${dcNode.name}")
          } else {
            log(s"Keeping the outer-pointer for Late-Closure-Class ${dcNode.name}")
          }
        }

      } // end of method squashOuterForLCC()

      /**
       *  The division of labor between `squashOuterForLCC()` and `forgetAboutOuter()` can be explained easily:
       *    (a) `forgetAboutOuter()` rewrites a Late-Closure-Class to remove outer pointer;
       *    (b) while `squashOuterForLCC()` does all the rest, includind determining which
       *        Late-Closure-Classes should be handed to `forgetAboutOuter()`.
       * */
      private def forgetAboutOuter(dcNode: ClassNode, epk: String) {

        // Step 1: outer field
        val of = JListWrapper(dcNode.fields).find(_.name == nme.OUTER.toString).get
        dcNode.fields.remove(of)

        // Step 2: first argument of <init>
        val ctor = JListWrapper(dcNode.methods).find(_.name == "<init>").get

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
          if(insn.getType == AbstractInsnNode.VAR_INSN) {
            val vi = insn.asInstanceOf[VarInsnNode]
            if(vi.`var` > 1) {
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
          if(getOuter.nonEmpty) {
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
          if(direct.nonEmpty) { walk(direct) }
        }
      }

      def toSourceValueArray(arr: Array[_ <: asm.tree.analysis.Value]): Array[SourceValue] = {
        arr map (_.asInstanceOf[SourceValue])
      }

      def descriptorWithoutOuter(desc: String): String = {
        val mt = BType.getMethodType(desc)
        val argsExceptHead = mt.getArgumentTypes.drop(1)
        val updatedDesc    = BType.getMethodDescriptor(mt.getReturnType, argsExceptHead)

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
                    if(!cp.hasUniqueImage(prod, consumer)) {
                        return false
                    }
                }
                true
            }

        def elideOuter(init: MethodInsnNode) {
          val f = frames(init)
          val actArgs = f.getActualArguments(init)
          val outerProds: SourceValue = toSourceValueArray(actArgs)(0)
          if(isSoleConsumer(outerProds.insns, init)) {
            dropAtSource(outerProds.insns)
          } else {
            // drop at sink
            val numberOfArgs = BType.getMethodType(init.desc).getArgumentCount
            dropStackElem(init, numberOfArgs - 1, 1)
          }
          val updatedDesc = descriptorWithoutOuter(init.desc)
          init.desc = updatedDesc
        }

        def elideReceiver(call: MethodInsnNode) {
          val f = frames(call)
          val rcvProds = f.getReceiver(call).asInstanceOf[SourceValue]
          if(isSoleConsumer(rcvProds.insns, call)) {
            dropAtSource(rcvProds.insns)
          } else {
            // drop at sink
            val numberOfArgs = BType.getMethodType(call.desc).getArgumentCount
            dropStackElem(call, numberOfArgs, 1)
          }
          call.setOpcode(Opcodes.INVOKESTATIC)
        }

        private def dropAtSource(producers: _root_.java.util.Set[_ <: AbstractInsnNode]) {
          val iter = producers.iterator()
          while(iter.hasNext) {
            val prod = iter.next
            if(Util.isLOAD(prod)) {
              mnode.instructions.remove(prod)
            } else {
              mnode.instructions.insert(prod, Util.getDrop(1))
            }
          }
        }

        /**
         *  Inserts STORE, POP, and LOAD, instructions so as to drop the n-th stack element counting from top starting at 0.
         *  E.g., dropStackElem(mi, 0, elemSize) amounts to dropping stack top
         *        dropStackElem(mi, 1, elemSize) drops the element pushed just before stack top, and so on.
         *
         *  As stated in analysis.Frame.getStackSize(), for the purposes of stack-indexing:
         *   "Long and double values are treated as single values."
         *
         * */
        private def dropStackElem(sink: MethodInsnNode, argsToSave: Int, elemSize: Int) {
          val mt     = BType.getMethodType(sink.desc)
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

      }

    } // end of class LCCOuterSquasher

    /**
     *  This version can cope with <init> super-calls (which are valid only in ctors) as well as
     *  with all code reductions the optimizer performs. This flexibility requires a producers-consumers analysis,
     *  which makes the rewriting slower than its counterpart in GenBCode.
     *
     *  @see long description at `rephraseBackedgesInCtorArg()`
     *
     *  @return true iff the method body was mutated
     * */
    final def rephraseBackedgesSlow(mnode: MethodNode): Boolean = {

      val inits =
        for(
          i <- mnode.instructions.toList;
          if i.getType == AbstractInsnNode.METHOD_INSN;
          mi = i.asInstanceOf[MethodInsnNode];
          if (mi.name == "<init>") && (mi.desc != "()V")
        ) yield mi;
      if (inits.isEmpty) { return false }

      val cp = ProdConsAnalyzer.create()
      cp.analyze(cnode.name , mnode)

      for(init <- inits) {
        val receiverSV: SourceValue = cp.frameAt(init).getReceiver(init)
        assert(
          receiverSV.insns.size == 1,
          s"A unique NEW instruction cannot be determined for ${insnPosInMethodSignature(init, mnode, cnode)}"
        )
        val dupInsn = receiverSV.insns.iterator().next()
        val bes: java.util.Map[JumpInsnNode, LabelNode] = Util.backedges(dupInsn, init)
        if(!bes.isEmpty) {
          val newInsn = dupInsn.getPrevious.asInstanceOf[TypeInsnNode]
          mnode.maxLocals = rephraseBackedgesInCtorArg(mnode.maxLocals, bes, cnode, mnode, newInsn, init)
        }
      }

      true
    } // end of method rephraseBackedgesSlow()

    //--------------------------------------------------------------------
    // Utilities for reuse by different optimizers
    //--------------------------------------------------------------------

    /**
     *  Well-formedness checks, useful after each fine-grained transformation step on a MethodNode.
     *
     *  Makes sure that exception-handler and local-variable entries aren't obviously wrong
     *  (e.g., the left and right brackets of instruction ranges are checked, right bracket should follow left bracket).
     */
    final def repOK(mnode: asm.tree.MethodNode): Boolean = {
      if(!global.settings.debug.value) {
        return true;
      }

          def isInsn(insn: asm.tree.AbstractInsnNode) {
            assert(mnode.instructions.contains(insn))
          }

          def inSequence(fst: asm.tree.AbstractInsnNode, snd: asm.tree.AbstractInsnNode): Boolean = {
            var current = fst
            while(true) {
              current = current.getNext()
              if(current == null) { return false }
              if(current == snd)  { return true  }
            }
            false
          }

      mnode foreachInsn { insn => assert(insn != null, "instruction stream shouldn't contain nulls.") }

      // exception-handler entries
      if(mnode.tryCatchBlocks != null) {
        val tryIter = mnode.tryCatchBlocks.iterator()
        while(tryIter.hasNext) {
          val tcb = tryIter.next
          assert(tcb.start   != null)
          assert(tcb.end     != null)
          assert(tcb.handler != null)
          isInsn(tcb.start)
          isInsn(tcb.end)
          isInsn(tcb.handler)
          inSequence(tcb.start, tcb.end)
        }
      }

      // local-vars entries
      if(mnode.localVariables != null) {
        val lvIter = mnode.localVariables.iterator()
        while(lvIter.hasNext) {
          val lv = lvIter.next
          isInsn(lv.start)
          isInsn(lv.end)
          inSequence(lv.start, lv.end)
        }
      }

      true
    }

    //--------------------------------------------------------------------
    // Type-flow analysis
    //--------------------------------------------------------------------

    final def runTypeFlowAnalysis(mnode: MethodNode) {

      import asm.tree.analysis.{ Analyzer, Frame }
      import asm.tree.AbstractInsnNode

      val tfa = new Analyzer[TFValue](new TypeFlowInterpreter)
      tfa.analyze(cnode.name, mnode)
      val frames: Array[Frame[TFValue]]   = tfa.getFrames()
      val insns:  Array[AbstractInsnNode] = mnode.instructions.toArray()
      var i = 0
      while(i < insns.length) {
        if (frames(i) == null && insns(i) != null) {
          // TODO abort("There should be no unreachable code left by now.")
        }
        i += 1
      }
    }

  } // end of class EssentialCleanser

  class QuickCleanser(cnode: asm.tree.ClassNode) extends EssentialCleanser(cnode) with QuickCleanserIface {

    val copyPropagator      = new asm.optimiz.CopyPropagator
    val deadStoreElim       = new asm.optimiz.DeadStoreElim
    val ppCollapser         = new asm.optimiz.PushPopCollapser
    val jumpReducer         = new asm.optimiz.JumpReducer
    val nullnessPropagator  = new asm.optimiz.NullnessPropagator
    val constantFolder      = new asm.optimiz.ConstantFolder

    //--------------------------------------------------------------------
    // First optimization pack
    //--------------------------------------------------------------------

    /**
     *  Intra-method optimizations performed until a fixpoint is reached.
     */
    final def basicIntraMethodOpt(mnode: asm.tree.MethodNode) {
      val cName = cnode.name
      var keepGoing = false
      do {
        keepGoing = false

        keepGoing |= cleanseMethod(cName, mnode)
        keepGoing |= elimRedundantCode(cName, mnode)

        nullnessPropagator.transform(cName, mnode);   // infers null resp. non-null reaching certain program points, simplifying control-flow based on that.
        keepGoing |= nullnessPropagator.changed

        constantFolder.transform(cName, mnode);       // propagates primitive constants, performs ops and simplifies control-flow based on that.
        keepGoing |= constantFolder.changed

      } while(keepGoing)
    }

    //--------------------------------------------------------------------
    // Second optimization pack
    //--------------------------------------------------------------------

    /**
     *  This method performs a few intra-method optimizations,
     *  aimed at reverting the extra copying introduced by inlining:
     *    - replace the last link in a chain of data accesses by a direct access to the chain-start.
     *    - dead-store elimination
     *    - remove those (producer, consumer) pairs where the consumer is a DROP and
     *      the producer has its value consumed only by the DROP in question.
     *
     * */
    final def elimRedundantCode(cName: String, mnode: asm.tree.MethodNode): Boolean = {
      var changed   = false
      var keepGoing = false

      do {

        keepGoing = false

        copyPropagator.transform(cName, mnode) // replace the last link in a chain of data accesses by a direct access to the chain-start.
        keepGoing |= copyPropagator.changed

        deadStoreElim.transform(cName, mnode)  // replace STOREs to non-live local-vars with DROP instructions.
        keepGoing |= deadStoreElim.changed

        ppCollapser.transform(cName, mnode)    // propagate a DROP to the instruction(s) that produce the value in question, drop the DROP.
        keepGoing |= ppCollapser.changed

        jumpReducer.transform(mnode)           // simplifies branches that need not be taken to get to their destination.
        keepGoing |= jumpReducer.changed

        changed = (changed || keepGoing)

      } while (keepGoing)

      changed
    }

  } // end of class QuickCleanser

  /**
   *  Intra-method optimizations. Upon visiting each method in an asm.tree.ClassNode,
   *  optimizations are applied iteratively until a fixpoint is reached.
   *
   *  All optimizations implemented here can do based solely on information local to the method
   *  (in particular, no lookups on `exemplars` are performed).
   *  That way, intra-method optimizations can be performed in parallel (in pipeline-2)
   *  while GenBCode's pipeline-1 keeps building more `asm.tree.ClassNode`s.
   *  Moreover, pipeline-2 is realized by a thread-pool.
   *
   *  The entry point is `cleanseClass()`.
   */
  final class BCodeCleanser(cnode: asm.tree.ClassNode, isInterClosureOptimizOn: Boolean) extends QuickCleanser(cnode) with BCodeCleanserIface {

    val unboxElider           = new asm.optimiz.UnBoxElider
    val lvCompacter           = new asm.optimiz.LocalVarCompact
    val unusedPrivateDetector = new asm.optimiz.UnusedPrivateDetector()

    /**
     *  Laundry-list of all optimizations that might possibly be applied
     *  ----------------------------------------------------------------
     *
     *  The intra-method optimizations below are performed until a fixpoint is reached.
     *  They are grouped somewhat arbitrarily into:
     *    - those performed by `cleanseMethod()`
     *    - those performed by `elimRedundandtCode()`
     *    - nullness propagation
     *    - constant folding
     *
     *  After the fixpoint has been reached, three more intra-method optimizations are performed just once
     *  (further applications wouldn't reduce any further):
     *    - eliding box/unbox pairs
     *    - eliding redundant local vars
     *
     *  Afterwards, some intra-class optimizations are performed repeatedly:
     *    - those private members of a class which see no use are elided
     *    - tree-shake unused closures, minimize the fields of those remaining
     *
     *  While other intra-class optimizations are performed just once:
     *    - minimization of closure-allocations
     *    - add caching for closure recycling
     *    - refresh the InnerClasses JVM attribute
     *
     *
     *  Fine print: Which optimizations are actually applied to which classes
     *  ---------------------------------------------------------------------
     *
     *  The above describes the common case, glossing over dclosure-specific optimizations.
     *  In fact, not all optimizations are applicable to any given ASM ClassNode, as described below.
     *
     *  The ClassNodes that reach `cleanseClass()` can be partitioned into:
     *    (1) master classes;
     *    (2) dclosures;
     *    (3) elided classes; and
     *    (4) none of the previous ones. Examples of (4) are:
     *        (4.a) a traditional closure lacking any dclosures, or
     *        (4.b) a plain class without dclosures.
     *
     *  The categories above make clear why:
     *    (a) an elided class need not be optimized (nobody will notice the difference)
     *        that's why `cleanseClass()` just returns on seeing one.
     *    (b) only master classes (and their dclosures) go through the following optimizations:
     *          - shakeAndMinimizeClosures()
     *          - minimizeDClosureAllocations()
     *        To recap, `cleanseClass()` executes in a Worker2 thread. The dclosure-specific optimizations are organized
     *        such that exclusive write access to a dclosure is granted to its master class (there's always one).
     *
     *  In summary, (1) and (4) should have the (chosen level of) optimizations applied,
     *  with (1) also amenable to dclosure-specific optimizations.
     *
     *  An introduction to ASM bytecode rewriting can be found in Ch. 8. "Method Analysis" in
     *  the ASM User Guide, http://download.forge.objectweb.org/asm/asm4-guide.pdf
     *
     *  TODO refreshInnerClasses() should also be run on dclosures
     */
    def cleanseClass() {

      // a dclosure is optimized together with its master class by `DClosureOptimizer`
      assert(!isDClosure(cnode.name), "A delegating-closure pretented to be optimized as plain class: " + cnode.name)

      val bt = lookupRefBType(cnode.name)
      if(elidedClasses.contains(bt)) { return }

      // (1) intra-method
      intraMethodFixpoints(full = true)

      val dcloptim =
        if(isInterClosureOptimizOn && isMasterClass(bt)) { new DClosureOptimizerImpl(cnode) }
        else null

      if(dcloptim != null) {

        var keepGoing = false
        do {

            // (2) intra-class, useful for master classes, but can by applied to any class.
            keepGoing  = removeUnusedLiftedMethods()

            // (3) inter-class but in a controlled way (any given class is mutated by at most one Worker2 instance).
            keepGoing |= dcloptim.shakeAndMinimizeClosures()

            if(keepGoing) { intraMethodFixpoints(full = false) }

        } while(keepGoing)

        dcloptim.minimizeDClosureAllocations()
      }

      for(mnode <- cnode.toMethodList; if Util.hasBytecodeInstructions(mnode)) {
        rephraseBackedgesSlow(mnode)
      }

    } // end of method cleanseClass()

    /**
     *  intra-method optimizations
     * */
    def intraMethodFixpoints(full: Boolean) {

      for(mnode <- cnode.toMethodList; if Util.hasBytecodeInstructions(mnode)) {

        Util.computeMaxLocalsMaxStack(mnode)

        basicIntraMethodOpt(mnode)                 // intra-method optimizations performed until a fixpoint is reached

        if(full) {
          unboxElider.transform(cnode.name, mnode) // remove box/unbox pairs (this transformer is more expensive than most)
          lvCompacter.transform(mnode)             // compact local vars, remove dangling LocalVariableNodes.
        }

        ifDebug { runTypeFlowAnalysis(mnode) }

      }

    }

    /**
     *  Elides unused private lifted methods (ie neither fields nor constructors) be they static or instance.
     *  How do such methods become "unused"? For example, dead-code-elimination may have removed all invocations to them.
     *
     *  Other unused private members could also be elided, but that might come as unexpected,
     *  ie a situation where (non-lifted) private methods vanish on the way from source code to bytecode.
     *
     *  Those bytecode-level private methods that originally were local (in the Scala sense)
     *  are recognized because isLiftedMethod == true.
     *  In particular, all methods originally local to a delegating-closure's apply() are private isLiftedMethod.
     *  (Sidenote: the endpoint of a dclosure is public, yet has isLiftedMethod == true).
     *
     * */
    private def removeUnusedLiftedMethods(): Boolean = {
      var changed = false
      unusedPrivateDetector.transform(cnode)
      for(im <- JSetWrapper(unusedPrivateDetector.elidableInstanceMethods)) {
        if(im.isLiftedMethod && !Util.isConstructor(im)) {
          changed = true
          cnode.methods.remove(im)
        }
      }

      changed
    }

  } // end of class BCodeCleanser

  /**
   * One of the intra-method optimizations (dead-code elimination)
   * and a few of the inter-procedural ones (inlining)
   * may have caused the InnerClasses JVM attribute to become stale
   * (e.g. some inner classes that were mentioned aren't anymore,
   * or inlining added instructions referring to inner classes not yet accounted for)
   *
   * This method takes care of SI-6546 "Optimizer leaves references to classes that have been eliminated by inlining"
   *
   * TODO SI-6759 Seek clarification about necessary and sufficient conditions to be listed in InnerClasses JVM attribute (GenASM).
   * The JVM spec states in Sec. 4.7.6 that
   *   for each CONSTANT_Class_info (constant-pool entry) which represents a class or interface that is not a member of a package
   * an entry should be made in the class' InnerClasses JVM attribute.
   * According to the above, the mere fact an inner class is mentioned in, for example, an annotation
   * wouldn't be reason enough for adding it to the InnerClasses JVM attribute.
   * However that's what GenASM does. Instead, this method scans only those internal names that will make it to a CONSTANT_Class_info.
   *
   * `refreshInnerClasses()` requires that `exemplars` already tracks
   * each BType of hasObjectSort variety that is mentioned in the ClassNode.
   *
   * can-multi-thread
   */
  final def refreshInnerClasses(cnode: ClassNode) {

    import scala.collection.convert.Wrappers.JListWrapper

    val refedInnerClasses = mutable.Set.empty[BType]
    cnode.innerClasses.clear()

        def visitInternalName(value: String) {
          if(value == null) {
            return
          }
          var bt = lookupRefBType(value)
          if (bt.isArray) {
            bt = bt.getElementType
          }
          if(bt.hasObjectSort && !bt.isPhantomType && (bt != BoxesRunTime) && !elidedClasses.contains(bt)) {
            if(exemplars.get(bt).isInnerClass) {
              refedInnerClasses += bt
            }
          }
        }

        def visitDescr(desc: String) {
          val bt = descrToBType(desc)
          if(bt.isArray) { visitDescr(bt.getElementType.getDescriptor) }
          else if(bt.sort == BType.METHOD) {
            visitDescr(bt.getReturnType.getDescriptor)
            bt.getArgumentTypes foreach { at => visitDescr(at.getDescriptor) }
          } else if(bt.hasObjectSort) {
            visitInternalName(bt.getInternalName)
          }
        }

    visitInternalName(cnode.name)
    visitInternalName(cnode.superName)
    JListWrapper(cnode.interfaces) foreach visitInternalName
    visitInternalName(cnode.outerClass)
    JListWrapper(cnode.fields)  foreach { fn: FieldNode  => visitDescr(fn.desc) }
    JListWrapper(cnode.methods) foreach { mn: MethodNode => visitDescr(mn.desc) }

    // annotations not visited because they store class names in CONSTANT_Utf8_info as opposed to the CONSTANT_Class_info that matter for InnerClasses.

    // TODO JDK8 the BootstrapMethodsAttribute may point via bootstrap_arguments to one or more CONSTANT_Class_info entries

    for(m <- JListWrapper(cnode.methods)) {

      JListWrapper(m.exceptions) foreach visitInternalName

      JListWrapper(m.tryCatchBlocks) foreach { tcb => visitInternalName(tcb.`type`) }

      val iter = m.instructions.iterator()
      while(iter.hasNext) {
        val insn = iter.next()
        insn match {
          case ti: TypeInsnNode   => visitInternalName(ti.desc) // an intenal name, actually
          case fi: FieldInsnNode  => visitInternalName(fi.owner); visitDescr(fi.desc)
          case mi: MethodInsnNode => visitInternalName(mi.owner); visitDescr(mi.desc)
          case ivd: InvokeDynamicInsnNode => () // TODO
          case ci: LdcInsnNode    =>
            ci.cst match {
              case t: asm.Type => visitDescr(t.getDescriptor)
              case _           => ()
            }
          case ma: MultiANewArrayInsnNode => visitDescr(ma.desc)
          case _ => ()
        }
      }

    }

    // cnode is a class being compiled, thus its Tracked.directMemberClasses should be defined
    // TODO check whether any member class has been elided? (but only anon-closure-classes can be elided)
    refedInnerClasses ++= exemplars.get(lookupRefBType(cnode.name)).directMemberClasses

    addInnerClassesASM(cnode, refedInnerClasses)

  } // end of method refreshInnerClasses()

} // end of class BCodeOptIntra