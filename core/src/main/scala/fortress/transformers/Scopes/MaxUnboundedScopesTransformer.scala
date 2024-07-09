package fortress.transformers

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.operations._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState


object MaxUnboundedScopesTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes
        
        //save all sorts that are quantified or have transitive closure applied to them
        var sortSet: Set[Sort] = Set.empty

        for( axiom <- theory.axioms ) {
            sortSet = sortSet ++ SimpleUnboundedChecker.getBoundedSort(axiom)
        }

        val new_scopes = scopes.filter( scope => { sortSet.contains(scope._1) } )
        /*
        ProblemState(
            theory,
            new_scopes,
            skc,
            skf,
            rangeRestricts,
            unapplyInterp,
            distinctConstants
        )
        */
        problemState.copy(scopes = new_scopes)

    }


}
