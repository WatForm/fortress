package fortress.tfol.operations

import fortress.tfol._

/** Accumulates the set of all symbol names used in the term, including free
  * variables and constants, bound variables (even useless ones that aren't
  * used in the body of the quantifier), function names, and sort names that
  * appear on variable bindings. */
object AllSymbols {
    def apply(term: Term): Set[String] = {
        def symbols(term: Term): Set[String] = term match {
            case Top | Bottom | DomainElement(_, _)
                | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set()
            case Var(x) => Set(x)
            case EnumValue(x) => Set(x)
            case Not(p) => symbols(p)
            case AndList(args) => args.map(symbols).reduce((a, b) => a union b)
            case OrList(args) => args.map(symbols).reduce((a, b) => a union b)
            case Distinct(args) => args.map(symbols).reduce((a, b) => a union b)
            case Implication(p, q) => symbols(p) union symbols(q)
            case Iff(p, q) => symbols(p) union symbols(q)
            case Eq(l, r) => symbols(l) union symbols(r)
            case App(fname, args) => args.map(symbols).reduce((a, b) => a union b) + fname
            case Forall(vars, body) => symbols(body) union vars.map(_.variable.name).toSet union vars.map(_.sort.name).toSet
            case Exists(vars, body) => symbols(body) union vars.map(_.variable.name).toSet union vars.map(_.sort.name).toSet
        }
        symbols(term)
    }
}
