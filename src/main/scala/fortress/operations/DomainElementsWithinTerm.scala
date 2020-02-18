package fortress.operations

import fortress.msfol._

/** Returns the set of all domain elements that appear within a term.
An exception is thrown if the term contains EnumValues, since you are probably
missing a step in the pipeline if there are still enum values but you care about
which domain elements exist. */
object DomainElementsWithinTerm {
    def apply(term: Term): Set[DomainElement] = domElems(term)
    
    private def domElems(term: Term): Set[DomainElement] = term match {
        case Top | Bottom | Var(_) 
            | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set()
        case de @ DomainElement(_, _) => Set(de)
        case EnumValue(_) => ???
        case Not(p) => domElems(p)
        case AndList(args) => args.map(domElems).reduce((a, b) => a union b)
        case OrList(args) => args.map(domElems).reduce((a, b) => a union b)
        case Distinct(args) => args.map(domElems).reduce((a, b) => a union b)
        case Implication(p, q) => domElems(p) union domElems(q)
        case Iff(p, q) => domElems(p) union domElems(q)
        case Eq(l, r) => domElems(l) union domElems(r)
        case App(fname, args) => args.map(domElems).reduce((a, b) => a union b)
        case BuiltinApp(function, args) => args.map(domElems).reduce((a, b) => a union b)
        case Forall(vars, body) => domElems(body)
        case Exists(vars, body) => domElems(body)
    }
}
