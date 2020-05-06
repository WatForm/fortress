package fortress.msfol

import fortress.util.Errors

case class Problem private (theory: Theory, scopes: Map[Sort, Int]) {
    Errors.precondition(scopes.values.forall(_ > 0), "Scopes must be positive")
    Errors.precondition(scopes.keySet.forall(!_.isBuiltin))
}
