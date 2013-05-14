/* NSC -- new Scala compiler
 * Copyright 2005-2013 LAMP/EPFL
 * @author
 */

package scala
package tools.nsc
package transform

import symtab.Flags._
import scala.collection.{ mutable, immutable }
import scala.language.postfixOps

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
trait LateClosureClasses { _: UnCurry =>

  import global._                  // the global environment
  import definitions._             // standard classes and methods

  var convertedTraditional = 0
  var convertedModern      = 0

  trait LCCTransformer { _: UnCurryTransformer =>

    val doConvertTraditional = settings.isClosureConvTraditional || settings.etaExpandKeepsStar.value


    /*
     *  Transform a function node (x_1,...,x_n) => body of type FunctionN[T_1, .., T_N, R] to
     *
     *  {
     *    def hoisted(x_1: T_1, ..., x_N: T_n): R = body
     *
     *    hoisted(zeroes-for-params-above).asInstanceOf[AbstractFunctionN[T_1, .., T_N, R]]
     *  }
     *
     *  The bytecode emitter will either:
     *    (a) emit an anonymous closure class and its instantiation; or
     *    (b) emit a method handle given as constructor-argument to a closure instantiation.
     *
     *
     *  Motivation
     *  ----------
     *
     *  By 'hoisting' the closure-body out of the anon-closure-class, lambdalift and explicitouter
     *  are prompted to add formal-params to convey values captured from the lexical environment.
     *  This amounts to 'scalar replacement of aggregates' that cuts down on heap-hops over outer() methods.
     *
     *  After lambdalift the hoisted method (now declared in a class `H`) can access H's fields directly (thus avoiding an $outer indirection).
     *  Similarly for values from outer instances.
     *
     *  On the other hand, both closure conversion approaches
     *  require IntRef and similar for captured-locals, but the Escape Analysis in the VM can stack-allocate them on its own:
     *    https://wikis.oracle.com/display/HotSpotInternals/EscapeAnalysis
     *    http://dl.acm.org/citation.cfm?id=945892
     *
     *  Under the "modern" closure-conversion scheme, loading anon-closure-classes is faster because there's less code to verify.
     *  It's true however that a "closures-via-invokedynamic" approach would further reduce that overhead
     *  (because materializing the inner class is delayed until runtime, see java/lang/invoke/LambdaMetafactory).
     *  Another approach is "method-handle wrapped-in-closure": instead of generating a custom inner class,
     *  all closure instances are obtained by instantiating a single common class whose single constructor argument is a MethodHandle.
     *
     *  For comparison, a discussion of the difficulties when attempting to stack-allocate closures
     *  under the `closureConversionTraditional()` secheme can be found at:
     *    https://groups.google.com/d/topic/scala-internals/Hnftko0MzDM/discussion
     *
     *  TODO SI-6666 , SI-6727 (pos/z1730) . Also: not a bug but beware: SI-6730
     *
     *  TODO Related approach: https://github.com/retronym/scala/compare/topic/closure-sharing
     *       Why not constrain isSafeToUseConstantFunction to just Function whose apply()'s body has constant type?
     *       Useful e.g. with assert(cond, msg) when msg is string literal
     *       (otherwise, the anon-closure-class refers to the enclosing method, which refers to inner classes chain, not to mention the ConstantPool grows, etc.)
     */
    def closureConversionModern(unit: CompilationUnit, fun: Function): Tree = {

      val targs = fun.tpe.typeArgs
      val (formals, restpe) = (targs.init, targs.last)
      val closureOwner = fun.symbol.owner

      val hoistedMethodDef: DefDef = {
        val hoistedName  = unit.freshTermName("dlgt$" + currentClass.fullName.hashCode.toHexString)
        val hoistmethSym = closureOwner.newMethod(hoistedName, fun.pos, inConstructorFlag | FINAL)
        val paramSyms = map2(formals, fun.vparams) {
          (tp, param) => hoistmethSym.newSyntheticValueParam(tp, param.name)
        }
        hoistmethSym setInfo MethodType(paramSyms, restpe)

        fun.vparams foreach  (_.symbol.owner =  hoistmethSym)
        fun.body changeOwner (fun.symbol     -> hoistmethSym)

        val hbody    = localTyper.typedPos(fun.pos)(fun.body)
        val hmethDef = DefDef(hoistmethSym, List(fun.vparams), hbody)

        // Have to repack the type to avoid mismatches when existentials
        // appear in the result - see SI-4869.
        hmethDef.tpt setType localTyper.packedType(hbody, hoistmethSym)
        hmethDef
      }

      val zeroes: List[Tree] = (formals map { frml =>
        if (isRepeatedParamType(frml)) { gen.sharedNullLiteral }
        else { gen.mkZero(frml) }
      })

      val fakeCallsite =
        Apply(
          definitions.lccDisguiserMethod,
          Apply(hoistedMethodDef.symbol, zeroes: _* )
        )

      assert(isFunctionType(fun.tpe), s"Found a Function node whose tpe isn't function type but ${fun.tpe}")
      val closureType: Type = abstractFunctionForFunctionType(fun.tpe) // Serializable not yet here

      val callDisguisedAsClosure = gen.mkAsInstanceOf(fakeCallsite, closureType, wrapInApply = false)

      localTyper.typedPos(fun.pos) {
        Block(
          hoistedMethodDef :: Nil,
          callDisguisedAsClosure
        )
      }
    } // end of method closureConversionModern()

    /*
     *  Currently closureConversionModern goes after closures with param-types that unproblematically
     *  accept either 0, false, or null, as valid values. Unlike the following example from test/files/run/byname.scala
     *
     *      private[this] val testAllR: (Int, => Int, Seq[Int]) => Int = {
     *           (x: Int,
     *            y: => Int,
     *            z: Seq[Int]) => Test.this.testAll(x, y, (z: _*))
     *         };
     *
     *  If left to its own devices, gen.mkZero builds stuff (for the 2nd param above, the by-name param)
     *  that after transformation by closureConversionModern gets stuck in the bytecode emitter.
     *
     *  TODO devise a less restrictive solution for the above.
     */
    def isAmenableToLateDelegatingClosures(fun: Function): Boolean = {
      val targs = fun.tpe.typeArgs
      val (formals, restpe) = (targs.init, targs.last)

      def isFineType(t: Type) = {
        (t.typeSymbol != NothingClass) && (t <:< AnyRefTpe) && !t.typeSymbol.isExistentiallyBound
      }

      val isFineResult = { isPrimitiveValueType(restpe) || isFineType(restpe) }

      if (!isFineResult) {
        return false // TODO debug
      }

      formals forall { frml =>
        val isNonUnitPrimitiveValueType = ScalaValueClassesNoUnit contains (frml.typeSymbol)

        isNonUnitPrimitiveValueType ||
        (isFineType(frml) && !isByNameParamType(frml))
      }
    } // end of method isAmenableToLateDelegatingClosures()

  }

}
