package fortress.transformers

import scala.jdk.CollectionConverters._
import fortress.msfol._
import fortress.operations.LiaChecker
import fortress.util.Errors
import fortress.operations.TermOps._
import fortress.problemstate.ProblemState
import fortress.problemstate.ExactScope
import fortress.problemstate.Scope
import fortress.interpretation.Interpretation

/** Replaces integers with bitvectors of the given bitwidth. */
object IntToBVTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = {
        var newProblemState = problemState

        if (problemState.scopes.contains(IntSort)) {
            val numValues = problemState.scopes(IntSort).size
            // Do log_2 of numValues to find bitwidth
            val bitwidth: Int = math.round(math.ceil(math.log(numValues) / math.log(2))).toInt
            // We may store more values than initially given
            val totalValues = math.pow(2, bitwidth).toInt

            val newAxioms = problemState.theory.axioms.map( axiom => {
                // isLia is a variable that is SET by a different transformer if we should skip.
                // TODO this is just a really bad way to do this in general, and we should change how LIA is handled
                // ESPECIALLY since we aren't really using it
                if( !axiom.isLia ) axiom.intToBitVector(bitwidth)
                else axiom
            })
            val (newSig, unapply) = problemState.theory.signature.replaceIntegersWithBitVectors(bitwidth)
            // remove IntSort from the scopes map
            val newScopes: Map[Sort, Scope] = problemState.scopes.filter(x => !(x._1 == IntSort)) + (BitVectorSort(bitwidth) -> ExactScope(totalValues))
            // change the theory
            newProblemState = problemState.withTheory(Theory(newSig, newAxioms)).withScopes(newScopes)
                .withUnapplyInterp(unapply)
        }

        /*
        if (problemState.scopes.contains(BoundedIntSort)) {
            val numValues = problemState.scopes(BoundedIntSort).size
            // Do log_2 of numValues to find bitwidth
            val bitwidth: Int = math.round(math.ceil(math.log(numValues) / math.log(2))).toInt
            // We may store more values than initially given
            val totalValues = math.pow(2, bitwidth).toInt

            val newAxioms = problemState.theory.axioms.map( axiom => {
                if( !axiom.isLia ) axiom.intToBitVector(bitwidth)
                else axiom
            })
            val (newSig, unapply) = problemState.theory.signature.replaceIntegersWithBitVectors(bitwidth)
            // remove IntSort from the scopes map
            val newScopes: Map[Sort, Scope] = problemState.scopes.filter(x => !(x._1 == BoundedIntSort)) + (BitVectorSort(bitwidth) -> ExactScope(totalValues))
            // this is the return value
            newProblemState = problemState.withTheory(Theory.mkTheoryWithSignature(newSig).withAxioms(newAxioms)).withScopes(newScopes)
                .withUnapplyInterp(unapply)

        }
        */

        newProblemState
    }
    

}
