package fortress.tfol.operations

import fortress.tfol._

object DomainElementEliminator {
    def apply(term: Term): Term = {
        def eliminateDomainElements(term: Term): Term = term match {
            case d @ DomainElement(_, _) => d.asSmtConstant
            case Not(p) => Not(eliminateDomainElements(p))
            case AndList(args) => AndList(args.map(eliminateDomainElements))
            case OrList(args) => OrList(args.map(eliminateDomainElements))
            case Implication(l, r) => Implication(eliminateDomainElements(l), eliminateDomainElements(r))
            case Distinct(args) => Distinct(args.map(eliminateDomainElements))
            case Iff(l, r) => Iff(eliminateDomainElements(l), eliminateDomainElements(r))
            case Eq(l, r) => Eq(eliminateDomainElements(l), eliminateDomainElements(r))
            case App(fname, args) => App(fname, args.map(eliminateDomainElements))
            case Exists(vars, body) => Exists(vars, eliminateDomainElements(body))
            case Forall(vars, body) => Forall(vars, eliminateDomainElements(body))
            case TC(relName, arg1, arg2) => TC(relName, eliminateDomainElements(arg1), eliminateDomainElements(arg2))
            case Top() | Bottom() | Var(_) => term
        }
        eliminateDomainElements(term)
    }
}
