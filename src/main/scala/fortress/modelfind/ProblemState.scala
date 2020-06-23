package fortress.modelfind

import fortress.msfol._
import fortress.util.Errors
import fortress.interpretation.Interpretation

case class ProblemState private(
    theory: Theory,
    scopes: Map[Sort, Int],
    skolemConstants: Set[AnnotatedVar],
    skolemFunctions: Set[FuncDecl],
    rangeRestrictions: Set[RangeRestriction],
    unapplyInterp: List[Interpretation => Interpretation]
) {
    Errors.precondition(scopes.values.forall(_ > 0), "Scopes must be positive")
    Errors.precondition(scopes.keySet.forall(!_.isBuiltin))
    // All scoped sorts are within the theory
    Errors.precondition(scopes.keySet subsetOf theory.sorts)
    
    // TODO add precondition that theory domain elements respect the scopes
}

object ProblemState {
    def apply(theory: Theory): ProblemState = ProblemState(theory, Map.empty)
    
    def apply(theory: Theory, scopes: Map[Sort, Int]): ProblemState = {
        // Compute the scopes for enum sorts
        val enumScopes = theory.signature.enumConstants.map {
            case (sort, enumValues) => sort -> enumValues.size
        }.toMap

        // Check there is no conflict between the enum scopes and the provided scopes
        Errors.precondition(fortress.util.Maps.noConflict(enumScopes, scopes))

        new ProblemState(
            theory,
            scopes ++ enumScopes,
            Set.empty,
            Set.empty,
            Set.empty,
            List.empty
        )
    }
}
