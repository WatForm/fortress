package fortress.transformers

import scala.jdk.CollectionConverters._
import fortress.msfol._
import fortress.operations.LiaChecker
import fortress.util.Errors
import fortress.operations.TermOps._
import fortress.problemstate.ProblemState

/** Replaces integers with bitvectors of the given bitwidth. */
object IntegerToBitVectorTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = {
        if (problemState.scopes.contains(IntSort)) {
            val bitwidth = problemState.scopes(IntSort)  // Scope
            val newAxioms = problemState.theory.axioms.map( axiom => {
                if( !axiom.isLia ) axiom.intToBitVector(bitwidth.size)
                else axiom
            })
            val newSig = problemState.theory.signature.replaceIntegersWithBitVectors(bitwidth.size)
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
