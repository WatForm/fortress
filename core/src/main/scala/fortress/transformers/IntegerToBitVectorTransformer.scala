package fortress.transformers

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.util.Errors
import fortress.operations.TermOps._

/** Replaces integers with bitvectors of the given bitwidth. */
object IntegerToBitVectorTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = {
        if (problemState.scopes.contains(IntSort)) {
            val bitwidth = problemState.scopes(IntSort)
            val newAxioms = problemState.theory.axioms.map(_.intToBitVector(bitwidth._1))
            val newSig = problemState.theory.signature.replaceIntegersWithBitVectors(bitwidth._1)
            // remove IntSort from the scopes map
            val newScopes = problemState.scopes.filter(x => !(x._1 == IntSort))
            // this is the return value
            problemState.withTheory(Theory.mkTheoryWithSignature(newSig).withAxioms(newAxioms)).withScopes(newScopes)
        } else {
            // Nothing to change: return what was passed in
            problemState
        }
    }
    
    override val name: String = "IntegerToBitVector Transformer"
}
