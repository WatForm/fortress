package fortress.modelfind

import fortress.msfol._
import fortress.util.Errors

case class ProblemState(
    theory: Theory,
    scopes: Map[Sort, Int],
    skolemConstants: Set[AnnotatedVar],
    skolemFunctions: Set[FuncDecl]
) {
    Errors.precondition(scopes.values.forall(_ > 0), "Scopes must be positive")
    Errors.precondition(scopes.keySet.forall(!_.isBuiltin))
    // All scoped sorts are within the theory
    Errors.precondition(scopes.keySet subsetOf theory.sorts)
    
    // TODO add precondition that theory domain elements respect the scopes
}

object ProblemState {
    def apply(theory: Theory): ProblemState = ProblemState(theory, Map.empty, Set.empty, Set.empty)
    
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
            Set.empty
        )
    }
}
