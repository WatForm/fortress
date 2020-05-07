package fortress.msfol

import fortress.util.Errors

case class Problem private (theory: Theory, scopes: Map[Sort, Int]) {
    Errors.precondition(scopes.values.forall(_ > 0), "Scopes must be positive")
    Errors.precondition(scopes.keySet.forall(!_.isBuiltin))
    // All scoped typed are within the theory
    Errors.precondition(scopes.keySet subsetOf theory.sorts)
    
    // TODO add precondition that theory domain elements respect the scopes
}

object Problem {
    def apply(theory: Theory, scopes: Map[Sort, Int]): Problem = {
        // Compute the scopes for enum sorts
        val enumScopes = theory.signature.enumConstants.map {
            case (sort, enumValues) => sort -> enumValues.size
        }.toMap

        // Check there is no conflict between the enum scopes and the provided scopes
        Errors.precondition(fortress.util.Maps.noConflict(enumScopes, scopes))

        new Problem(theory, scopes ++ enumScopes)
    }
}
