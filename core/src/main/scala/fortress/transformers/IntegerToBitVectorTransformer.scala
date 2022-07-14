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
            val newAxioms = problemState.theory.axioms.map(_.finitizeIntegers(bitwidth))
            val newSig = problemState.theory.signature.replaceIntegersWithBitVectors(bitwidth)
            // this is the return value
            problemState.withTheory(Theory.mkTheoryWithSignature(newSig).withAxioms(newAxioms))
        } else {
            // Nothing to change: return what was passed in
            problemState
        }
    }
    
    override val name: String = "IntegerToBitVector Transformer"
}
