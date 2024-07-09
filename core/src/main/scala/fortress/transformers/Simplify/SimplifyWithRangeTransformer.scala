package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.problemstate.ProblemState

class SimplifyWithRangeTransformer extends ProblemStateTransformer {
        
    def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val rangeRestricts = problemState.rangeRestrictions

        val newTheory = theory.mapAllTerms(_.simplifyWithRange(rangeRestricts))
        // val newTheory = theory.mapAxioms(_.simplify)
        // ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants)
        problemState.copy(theory=newTheory)
    }
    

    
}
