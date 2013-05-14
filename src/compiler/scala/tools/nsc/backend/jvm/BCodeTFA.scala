/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */

package scala
package tools.nsc
package backend.jvm

import scala.tools.asm
import scala.annotation.switch
import scala.collection.{ immutable, mutable }

/*
 *  Type-flow Analysis.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded
 *  @version 1.0
 *
 */
abstract class BCodeTFA extends BCodeOptCommon {

  import global._

  var TF_NULL   : TFValue = null
  var TF_STRING : TFValue = null

  def initBCodeOpt() {

    initBCodeTypes()

    TF_NULL = TFValue(RT_NULL, 0)
    val trString = exemplar(global.definitions.StringClass)
    TF_STRING = TFValue(StringReference, TypeFlowConstants.EXACT_MASK)
  }

  /*
   *  Represents a lattice element in the type-flow lattice.
   *  For reference-values two additional information items are also tracked:
   *     - their non-nullness status
   *     - whether the runtime value has `btype` as exact type
   *       (useful in determining method implementations targeted by callsites)
   */
  case class TFValue(lca: BType, bits: Int) extends asm.tree.analysis.Value {

    val tr: Tracked = {
      if (lca.isPhantomType || lca.isValueType) { null }
      else if (lca.isArray)  {
        val et = lca.getElementType
        if (et.hasObjectSort) exemplars.get(et) else null
      }
      else {
        assert(lca.isNonSpecial, "Some case was overlooked for: " + lca)
        exemplars.get(lca)
      }
    }

    // check (when possible) cross-consistency with isExact and isNonNull
    assert(if (lca.isNullType) !isNonNull else true, "Contradiction: NullType reported as isNonNull." + lca)
    assert(if (tr != null && tr.isFinal)      isExact    else true, "Contradiction: isFinal  reported as !isExact."  + lca)
    assert(if (tr != null && tr.isInterface)  !isExact   else true, "Contradiction: interface reported as isExact."  + lca)

    override def getSize: Int = {
      assert(lca.sort != asm.Type.METHOD, "Method types don't have size: " + lca)
      lca.getSize
    }

    def isRefOrArray: Boolean = { lca.isRefOrArrayType }

    def isNonNull:  Boolean = { assert(isRefOrArray); (bits & TypeFlowConstants.NON_NULL_MASK) != 0 }
    def isExact:    Boolean = { assert(isRefOrArray); (bits & TypeFlowConstants.EXACT_MASK   ) != 0 }

    def conformsTo(b: TFValue): Boolean = { conforms(this.lca, b.lca) }

  }

  val TF_INT     = TFValue(BType.INT_TYPE,    0)
  val TF_FLOAT   = TFValue(BType.FLOAT_TYPE,  0)
  val TF_LONG    = TFValue(BType.LONG_TYPE,   0)
  val TF_DOUBLE  = TFValue(BType.DOUBLE_TYPE, 0)
  val TF_VOID    = TFValue(BType.VOID_TYPE,   0)

  object TypeFlowConstants {
    val NON_NULL_MASK = 1
    val EXACT_MASK    = 2
  }

  /*
   *  Can be used to compute a type-flow analysis for an asm.tree.MethodNode, as in: `tfa.analyze(owner, mnode)`
   *  The abstract state, right before each instruction, comprises abstract values
   *  for each local variable and for each position in the operand stack.
   *
   *  All methods in this class can-multi-thread
   **/
  class TypeFlowInterpreter extends asm.optimiz.InterpreterSkeleton[TFValue] {

    override def newValue(t: asm.Type): TFValue = {
      if (t == null || t == asm.Type.VOID_TYPE) { null }
      else { newValue(toBType(t)) }
    }

    private def newValue(t: BType): TFValue = {
      newValue(t, isExact = false, isKnownToBeNonNull = false)
    }

    private def newValue(t: BType, isExact: Boolean, isKnownToBeNonNull: Boolean): TFValue = {
      if (t == null || t.isUnitType) {
        return null
      }
      (t.sort: @switch) match {
        case asm.Type.VOID    => return TF_VOID
        case asm.Type.BOOLEAN |
             asm.Type.CHAR    |
             asm.Type.BYTE    |
             asm.Type.SHORT   |
             asm.Type.INT     => return TF_INT
        case asm.Type.FLOAT   => return TF_FLOAT
        case asm.Type.LONG    => return TF_LONG
        case asm.Type.DOUBLE  => return TF_DOUBLE
        case _ => ()
      }

      val lca   = t
      var isFinal = false

      if (!lca.isPhantomType && !lca.isValueType) {
        if (lca.hasObjectSort) {
          isFinal = exemplars.get(lca).isFinal
        } else if (lca.isArray) {
          val et = lca.getElementType
          if (!et.isPhantomType && et.hasObjectSort) {
            isFinal = exemplars.get(et).isFinal
          }
        } else { abort("Unexpected.") }
      }

      var bits = 0
      bits |= (if (isFinal || isExact) TypeFlowConstants.EXACT_MASK     else 0)
      bits |= (if (isKnownToBeNonNull) TypeFlowConstants.NON_NULL_MASK  else 0)

      TFValue(lca, bits)
    }

    /*
     *  The ICode counterpart is `typeLattice.lub2()`
     */
    override def merge(v: TFValue, w: TFValue): TFValue = {

      if (v == null) return w;
      if (w == null) return v;

      val lub: BType = {
        val a: BType = v.lca
        val b: BType = w.lca

        if      (a.isValueType)   { maxValueType(a, b)   }
        else if (a.isNothingType) { b }
        else if (b.isNothingType) { a }
        else {

          assert(a.isRefOrArrayType, "This is not a valuetype and it's not something else, what is it? " + a)
          assert(b.isRefOrArrayType, "Attempting to merge " + b + " with " + a)

          if (a.isNullType)      { b }
          else if (b.isNullType) { a }
          else if (a == b)       { a }
          else {
            if (a.isArray || b.isArray) { arrayLUB(a, b) }
            else {
              assert(a.hasObjectSort, "Expecting non-array referene, received: " + a)
              assert(b.hasObjectSort, "Expecting non-array referene, received: " + b)
              firstCommonSuffix(v.tr :: v.tr.superClasses, w.tr :: w.tr.superClasses)
            }
          }

        }
      }

      val bothRefOrArray = (v.isRefOrArray && w.isRefOrArray)

      val isExact   =
        if (bothRefOrArray) {
          if (v.lca.isNullType)      { w.isExact }
          else if (w.lca.isNullType) { v.isExact }
          else {
            v.isExact && w.isExact && (lub == v.lca) && (lub == w.lca)
          }
        } else false;

      val isNonNull = (bothRefOrArray && v.isNonNull && w.isNonNull)

      var bits = 0
      bits |= (if (isExact)   TypeFlowConstants.EXACT_MASK    else 0)
      bits |= (if (isNonNull) TypeFlowConstants.NON_NULL_MASK else 0)

      TFValue(lub, bits)
    }

    def arrayLUB(x: BType, y: BType): BType = {
      val xArr = x.isArray
      val yArr = y.isArray
      assert(xArr || yArr, "Precondition not fulfilled.")
      if (xArr && yArr) {
        val xCT = x.getComponentType
        val yCT = y.getComponentType
        if (xCT == yCT) { x }
        else {
          // the Oracle JVM implementation represents both [B and [Z as byte-array. But anyway we consider them unrelated.
          if      (xCT.isValueType || yCT.isValueType) { ObjectReference }
          else if (xCT.isArray     || yCT.isArray    ) {
            // TODO we could try `arrayOf(arrayLUB(xCT, yCT))` but lookupTypeName needs to lock chrs for that. Yes, buying into Java-wise array subtyping.
            ObjectReference
          }
          else {
            assert(xCT.hasObjectSort, "Expecting non-array referene, received: " + xCT)
            assert(yCT.hasObjectSort, "Expecting non-array referene, received: " + yCT)
            // TODO we could try `arrayOf(refLUB(xCT, yCT))` but lookupTypeName needs to lock chrs for that. Yes, buying into Java-wise array subtyping.
            objArrayReference
          }
        }
      }
      else { ObjectReference }
    }

    override def copyOperation(insn: asm.tree.AbstractInsnNode,
                               value: TFValue): TFValue = {
      value
    }

    override def naryOperation(insn: asm.tree.AbstractInsnNode,
                               values: java.util.List[_ <: TFValue]): TFValue = {
      insn match {
        case mna: asm.tree.MultiANewArrayInsnNode => newValue(asm.Type.getType(mna.desc))
        case ivd: asm.tree.InvokeDynamicInsnNode  => newValue(asm.Type.getReturnType(ivd.desc))
        case mni: asm.tree.MethodInsnNode =>
          // INVOKEVIRTUAL, INVOKESPECIAL, INVOKESTATIC, INVOKEINTERFACE
          val rt = asm.Type.getReturnType(mni.desc)
          if (rt == asm.Type.VOID_TYPE) null // will be discarded anyway by asm.tree.analysis.Frame.execute
          else newValue(rt)
      }
    }

    override def returnOperation(insn:     asm.tree.AbstractInsnNode,
                                 value:    TFValue,
                                 expected: TFValue) {
      ()
    }

    override def ternaryOperation(insn:   asm.tree.AbstractInsnNode,
                                  value1: TFValue,
                                  value2: TFValue,
                                  value3: TFValue): TFValue = {
      null
    }

    override def nullValue()   = TF_NULL
    // TODO also desirable: B, C, S, Z
    override def intValue()    = TF_INT
    override def longValue()   = TF_LONG
    override def floatValue()  = TF_FLOAT
    override def doubleValue() = TF_DOUBLE
    override def stringValue() = TF_STRING

    override def opAALOAD(insn: asm.tree.InsnNode, arrayref: TFValue, index: TFValue): TFValue = {
      newValue(arrayref.lca.getComponentType)
    }

    override def opNEW(insn: asm.tree.TypeInsnNode): TFValue = {
      newValue(lookupRefBType(insn.desc), isExact = true, isKnownToBeNonNull = true)
    }
    override def opANEWARRAY(insn: asm.tree.TypeInsnNode): TFValue = {
      val c: Char = insn.desc(0)
      assert(c != '(', "Unexpected method type: " + insn.desc)
      val arrType =
        if (c == '[') { "["  + insn.desc }
        else          { "[L" + insn.desc + ";" }
      newValue(lookupRefBType(arrType))
    }

    override def opCHECKCAST(insn: asm.tree.TypeInsnNode): TFValue = {
      val argument = lookupRefBType(insn.desc)
      /* Rather than always sticking to `argument` as done below,
       * TODO compare argument against stack-top to pick the more precise type:
       *   - when downcasting, the argument;
       *   - when upcasting, stack-top.
       */
      newValue(argument)
    }

    override def opGETFIELD(insn: asm.tree.FieldInsnNode, objectref: TFValue):                 TFValue =  { newValue(descrToBType(insn.desc)) }
    override def opPUTFIELD(insn: asm.tree.FieldInsnNode, objectref: TFValue, value: TFValue): TFValue =  { value }

    override def opGETSTATIC(insn: asm.tree.FieldInsnNode):                 TFValue = { newValue(descrToBType(insn.desc)) }
    override def opPUTSTATIC(insn: asm.tree.FieldInsnNode, value: TFValue): TFValue = { value }

    override def opLDCHandleValue(insn: asm.tree.AbstractInsnNode,     cst: asm.Handle): TFValue = { ??? }
    override def opLDCMethodTypeValue(insn: asm.tree.AbstractInsnNode, cst: asm.Type):   TFValue = { ??? }

    override def opLDCRefTypeValue(insn: asm.tree.AbstractInsnNode,    cst: asm.Type):   TFValue = { newValue(toBType(cst)) }

  }

}
