package fortress.msfol

import fortress.util.Errors

case class Problem private (theory: Theory, scopes: Map[Sort, Int]) {
    Errors.precondition(scopes.values.forall(_ > 0), "Scopes must be positive")
    Errors.precondition(scopes.keySet.forall(!_.isBuiltin))
    // All scoped typed are within the theory
    Errors.precondition(scopes.keySet subsetOf theory.sorts)
    
    // TODO add precondition that theory domain elements respect the scopes
}
