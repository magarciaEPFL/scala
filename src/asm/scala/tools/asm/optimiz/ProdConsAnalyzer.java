/* NSC -- new Scala compiler
 * Copyright 2005-2012 LAMP/EPFL
 * @author  Martin Odersky
 */


package scala.tools.asm.optimiz;

import java.util.Set;
import java.util.Iterator;
import java.util.Queue;
import java.util.LinkedList;

import scala.tools.asm.Opcodes;
import scala.tools.asm.tree.*;

import scala.tools.asm.tree.analysis.Analyzer;
import scala.tools.asm.tree.analysis.AnalyzerException;
import scala.tools.asm.tree.analysis.SourceValue;
import scala.tools.asm.tree.analysis.Frame;
/**
 *  A SourceInterpreter can be used in conjunction with an Analyzer
 *  to compute, for each instruction, a Frame containing for each location P
 *  (local-var or stack-slot) the instructions that may produce the value in P.
 *
 *  Oftentimes, we want to invert that map
 *  ie we want to find all the possible consumers of values that a given instruction produces.
 *
 *  After `analyze()` has run:
 *    - consumers(insn) returns the set of instructions that may consume at least one value produced by `insn`.
 *                      "at least" because DUP produces two values.
 *    - producers(insn) returns the set of instructions that may produce at least one value consumed by `insn`.
 *
 *  Alternative terminology:
 *     - those definitions reaching insn are given by `producers(insn)`
 *
 *  This in turn allows computing:
 *      - du-chains (definition-use chains)
 *      - ud-chains (use-definition chains)
 *      - webs
 *      as covered in Sec. 8.10 of
 *        Steven S. Muchnick. Advanced compiler design and implementation.
 *        Morgan Kaufmann Publishers Inc., San Francisco, CA, USA, 1997.
 *
 *  @author  Miguel Garcia, http://lamp.epfl.ch/~magarcia/ScalaCompilerCornerReloaded/
 *  @version 1.0
 *
 */
public class ProdConsAnalyzer extends Analyzer<SourceValue> {

    public static ProdConsAnalyzer create() {
        return new ProdConsAnalyzer(new ProdConsInterpreter());
    }

    private final ProdConsInterpreter pt;

    public ProdConsAnalyzer(ProdConsInterpreter pt) {
        super(pt);
        this.pt = pt;
    }

    MethodNode mnode = null;
    Frame<SourceValue>[] frames = null;

    // ------------------------------------------------------------------------
    // utilities made available to clients
    // ------------------------------------------------------------------------

    public Frame<SourceValue>[] analyze(final String owner, final MethodNode mnode) throws AnalyzerException {
        this.mnode = mnode;
        frames = super.analyze(owner, mnode);
        return frames;
    }

    public Frame<SourceValue> frameAt(AbstractInsnNode insn) {
        int idx = mnode.instructions.indexOf(insn);
        return frames[idx];
    }

    /**
     *  returns the instructions that may produce the value(s) that the argument consumes.
     * */
    public Set<AbstractInsnNode> producers(final AbstractInsnNode insn) {
        return pt.producers(insn);
    }

    /**
     *  returns the instructions that may consume the value(s) that the argument produces.
     * */
    public Set<AbstractInsnNode> consumers(final AbstractInsnNode insn) {
        return pt.consumers(insn);
    }

        // ------------------------------------------------------------------------
        // functionality used by PushPopCollapser
        // ------------------------------------------------------------------------

    public boolean isSoleConsumerForItsProducers(InsnNode consumer) {
        Set<AbstractInsnNode> ps = pt.producers(consumer);
        if(ps.isEmpty()) {
            // a POP as firs instruction of an exception handler should be left as-is
            // (its distinctive feature being a lack of explicit producers, ie the exception on the stack is loaded implicitly).
            return false;
        }
        Iterator<AbstractInsnNode> iter = ps.iterator();
        while (iter.hasNext()) {
            AbstractInsnNode prod = iter.next();
            if(!hasAsSingleConsumer(prod, consumer)) {
                return false;
            }
        }
        return true;
    }

    public boolean hasAsSingleConsumer(AbstractInsnNode producer, AbstractInsnNode consumer) {
        Set<AbstractInsnNode> cs = pt.consumers(producer);
        boolean result = (cs.size() == 1) && (cs.iterator().next().equals(consumer));
        return result;
    }

        // ------------------------------------------------------------------------
        // functionality used by UnBoxElider
        // ------------------------------------------------------------------------

    /**
     *  Given a `consumer` instruction, finds all its producers, for each all its consumers, for each all its producers,
     *  and so on until a fixpoint is reached. End results are returned in `allProducers` and `allConsumers`.
     *
     * */
    public void fixpointGivenConsumer(AbstractInsnNode consumer, Set<AbstractInsnNode> allProducers, Set<AbstractInsnNode> allConsumers) {

        Queue<AbstractInsnNode> cq = new LinkedList<AbstractInsnNode>();
        Queue<AbstractInsnNode> pq = new LinkedList<AbstractInsnNode>();

        cq.add(consumer);

        do {

            Iterator<AbstractInsnNode> iterProd = pq.iterator();
            while (iterProd.hasNext()) {
                AbstractInsnNode p = iterProd.next();
                allProducers.add(p);
                Set<AbstractInsnNode> cs = consumers(p);
                Iterator<AbstractInsnNode> iterCons = cs.iterator();
                while(iterCons.hasNext()) {
                    AbstractInsnNode c = iterCons.next();
                    if(!allConsumers.contains(c)) {
                        cq.add(c);
                    }
                }
            }
            pq.clear();

            Iterator<AbstractInsnNode> iterCons = cq.iterator();
            while (iterCons.hasNext()) {
                AbstractInsnNode c = iterCons.next();
                allConsumers.add(c);
                Set<AbstractInsnNode> ps = producers(c);
                iterProd = ps.iterator();
                while(iterProd.hasNext()) {
                    AbstractInsnNode p = iterProd.next();
                    if(!allProducers.contains(p)) {
                        pq.add(p);
                    }
                }
            }
            cq.clear();


        } while(!pq.isEmpty() || !cq.isEmpty());




    }

    // ------------------------------------------------------------------------
    // internal methods
    // ------------------------------------------------------------------------

}
