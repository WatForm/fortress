package fortress.transformers

import scala.jdk.CollectionConverters._
import fortress.msfol._
import fortress.operations.LiaChecker
import fortress.util.Errors
import fortress.operations.TermOps._
import fortress.problemstate.ProblemState
import fortress.problemstate.ExactScope
import fortress.problemstate.Scope

/** Replaces integers with bitvectors of the given bitwidth. */
object IntegerToBitVectorTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = {
        if (problemState.scopes.contains(IntSort)) {
            val numValues = problemState.scopes(IntSort).size
            // Do log_2 of numValues to find bitwidth
            val bitwidth: Int = math.round(math.ceil(math.log(numValues) / math.log(2))).toInt
            // We may store more values than initially given
            val totalValues = math.pow(2, bitwidth).toInt

            val newAxioms = problemState.theory.axioms.map( axiom => {
                if( !axiom.isLia ) axiom.intToBitVector(bitwidth)
                else axiom
            })
            val newSig = problemState.theory.signature.replaceIntegersWithBitVectors(bitwidth)
            // remove IntSort from the scopes map
            val newScopes: Map[Sort, Scope] = problemState.scopes.filter(x => !(x._1 == IntSort)) + (BitVectorSort(bitwidth) -> ExactScope(totalValues))
            // this is the return value
            problemState.withTheory(Theory.mkTheoryWithSignature(newSig).withAxioms(newAxioms)).withScopes(newScopes)

        } else {
            // Nothing to change: return what was passed in
            problemState
        }
    }
    
    override val name: String = "IntegerToBitVector Transformer"
}
