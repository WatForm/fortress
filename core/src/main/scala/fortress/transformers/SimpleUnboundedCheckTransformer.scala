package fortress.transformers

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.operations._
import fortress.operations.TheoryOps._


class SimpleUnboundedCheckTransformer extends ProblemStateTransformer {
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            //save all sorts that are quantified or have transitive closure applied to them
            var sortSet: Set[Sort] = Set.empty

            for( axiom <- theory.axioms ) {
                sortSet = sortSet ++ SimpleUnboundedChecker.getBoundedSort(axiom)
            }

            val new_scopes = scopes.filter( scope => { sortSet.contains(scope._1) } )

            ProblemState(
                theory,
                new_scopes,
                skc,
                skf,
                rangeRestricts,
                unapplyInterp,
                distinctConstants
            )

        }
    }

    override def name: String = "Simple Unbounded Check Transformer"
}
