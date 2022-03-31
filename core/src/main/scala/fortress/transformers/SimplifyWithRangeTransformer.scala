package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation

class SimplifyWithRangeTransformer extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            val newTheory = theory.mapAxioms(_.simplifyWithRange(rangeRestricts))
            // val newTheory = theory.mapAxioms(_.simplify)
            ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants)
        }
    }
    
    val name: String = "Simplify (with range) Transformer"
    
}
