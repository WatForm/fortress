package fortress.msfol.operations

import fortress.msfol._

/** Accumulates the free variables of a term. Note that this only considers the
  * term as a block of syntax, without respect to a signature, so a free variable
  * here may be bound as a constant of a theory. */
object FreeVariables {
    def apply(term: Term): Set[Var] = {
        def fv(term: Term): Set[Var] = term match {
            case Top | Bottom | DomainElement(_, _)
                | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set()
            case v @ Var(x) => Set(v)
            case EnumValue(x) => Set() 
            case Not(p) => fv(p)
            case AndList(args) => args.map(fv).reduce((a, b) => a union b)
            case OrList(args) => args.map(fv).reduce((a, b) => a union b)
            case Distinct(args) => args.map(fv).reduce((a, b) => a union b)
            case Implication(p, q) => fv(p) union fv(q)
            case Iff(p, q) => fv(p) union fv(q)
            case Eq(l, r) => fv(l) union fv(r)
            case App(f, args) => args.map(fv).reduce((a, b) => a union b)
            case Exists(vars, body) => fv(body) diff vars.map(_.variable).toSet
            case Forall(vars, body) => fv(body) diff vars.map(_.variable).toSet
        }
        fv(term)
    }
}
