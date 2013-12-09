/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.nsc.backend.bcode;

import java.util.*;

import scala.tools.asm.Type;
import scala.tools.asm.MethodVisitor;

import scala.tools.asm.tree.*;

import scala.tools.asm.tree.analysis.SourceValue;

/**
 *  A DisambiguatingAnalyzer goes one step further than its super-class (ProdConsAnalyzer)
 *  in that a more accurate tracking of absrtact values (when analyzing a method) is performed.
 *
 *  In detail, the sources of values received via method-params and local-vars
 *  are disambiguated: the former are known to have been assigned, unlike the latter.
 *
 *  The "disambiguation" in question is achieved by associating a fictitious "source instruction"
 *  as producer of a formal-param value.
 *
 *  A DisambiguatingAnalyzer is almost always used in pair with a DisambiguatingInterpreter,
 *  given that we want to track values (distinguishing sources of arguments from, say, local-vars)
 *  and for "tracking values" a copy-propagating override of ProdConsInterpreter.copyOperation()
 *  is needed.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class DisambiguatingAnalyzer extends ProdConsAnalyzer {

    public static DisambiguatingAnalyzer create() {
        return new DisambiguatingAnalyzer(new DisambiguatingInterpreter());
    }

    private final DisambiguatingInterpreter pt;

    public DisambiguatingAnalyzer(DisambiguatingInterpreter pt) {
        super(pt);
        this.pt = pt;
    }

    // ------------------------------------------------------------------------
    // internal methods
    // ------------------------------------------------------------------------

    @Override
    public SourceValue newFormal(boolean isInstanceMethod, int idx, Type ctype) {
        assert ctype != Type.VOID_TYPE;
        final int size = (ctype == null) ? 1 : ctype.getSize();
        return new SourceValue(size, new FakeParamLoad(idx, ctype, isInstanceMethod));
    }

    @Override
    public SourceValue newNonFormalLocal(int idx) {
        final int size = 1;
        return new SourceValue(size, new Uninitialized());
    }

    /**
     *  Serves the purpose of "materializing" the sources of:
     *    (a) local-vars standing for params (as well as THIS) and
     *    (b) the exceptions caught by exception handlers
     *
     *  Otherwise, the listing of producer instructions in a given SourceValue might miss to inform:
     *  that a xLOAD_n for a param should also be considered. Similarly for an exception handler.
     * */
    static public abstract class FakeInsn extends AbstractInsnNode {

        public boolean isThisRef()     { return false; }
        public boolean isFormalParam() { return false; }
        public boolean isEHException() { return false; }

        public FakeInsn() {
            super(-1);
        }

        @Override
        final public int getType() {
            throw new UnsupportedOperationException();
            // return VAR_INSN; // these fake instructions are akin to loads from locals. Approximately.
        }

        @Override
        final public void accept(MethodVisitor cv) {
            throw new UnsupportedOperationException();
        }

        @Override
        final public AbstractInsnNode clone(Map<LabelNode, LabelNode> labels) {
            throw new UnsupportedOperationException();
        }
    }

    final static public class FakeParamLoad extends FakeInsn {

        final public int idx;
        final public Type ctype;
        final public boolean isInstanceMethod;

        public FakeParamLoad(final int idx, final Type ctype, final boolean isInstanceMethod) {
            this.idx   = idx;
            this.ctype = ctype;
            this.isInstanceMethod = isInstanceMethod;
        }

        @Override final public boolean isThisRef()     { return isInstanceMethod && (idx == 0); }
        @Override final public boolean isFormalParam() { return !isThisRef(); }

    }

    final static public class FakeEHLoad extends FakeInsn {

        final public TryCatchBlockNode tcb;
        final public Type ctype;

        public FakeEHLoad(final TryCatchBlockNode tcb, final Type ctype) {
            this.tcb   = tcb;
            this.ctype = ctype;
        }

        @Override final public boolean isEHException() { return true; }

    }

    final static public class Uninitialized extends FakeInsn { }

    static private class DisambiguatingInterpreter extends ProdConsInterpreter {

        /**
          *  Unlike the overridden version, a LOAD of a local-var does not register itself
          *  as consumer of its producer and producer of its consumer (really).
          *  Instead, "it just becomes transparent" and passes over (unmodified) the received set of producers.
          *
          *  Together with the DisambiguatingAnalyzer.newLocal() override, this override makes a difference when copyOperation() handles a "LOAD param".
          *  The DisambiguatingAnalyzer override makes sure the SourceValue (for "LOAD param") contains a FakeParamLoad instruction
          *  (without such override, for a param not re-assigned in this method, that set is empty).
          *
          * */
        @Override
        public SourceValue copyOperation(final AbstractInsnNode insn, final SourceValue value) {
            return value;
        }

    } // end of class DisambiguatingInterpreter

} // end of class DisambiguatingAnalyzer
