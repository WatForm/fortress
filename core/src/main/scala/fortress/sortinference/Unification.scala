package fortress.sortinference

import fortress.msfol._
import fortress.util.Errors

object Unification {

    type SortVar = SortConst

    def unify(equations: List[Equation]): SortSubstitution = equations match {
        case Nil => SortSubstitution.identity
        case eqn :: eqns => eqn match {
            case Equation(s, t) if s == t => unify(eqns)
            case Equation(x: SortVar, t) => {
                val x_to_t = SortSubstitution.singleton(x -> t)
                unify(eqns map (x_to_t(_))) compose x_to_t
            }
            case Equation(s, x: SortVar) => {
                val x_to_s = SortSubstitution.singleton(x -> s)
                unify(eqns map (x_to_s(_))) compose x_to_s
            }
            case _ => {
                ???
            }
        } 
    }
}
