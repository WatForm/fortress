package fortress.msfol.operations

import fortress.msfol._

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
            case BuiltinApp(function, args) => args.map(symbols).reduce((a, b) => a union b)
            case Forall(vars, body) => symbols(body) union vars.map(_.variable.name).toSet union vars.map(_.sort.name).toSet
            case Exists(vars, body) => symbols(body) union vars.map(_.variable.name).toSet union vars.map(_.sort.name).toSet
        }
        symbols(term)
    }
}

object SymbolAccumulator {
    def functionsIn(term: Term): Set[String] = term match {
        case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set()
        case Not(p) => functionsIn(p)
        case AndList(args) => args.map(functionsIn).reduce((a, b) => a union b)
        case OrList(args) => args.map(functionsIn).reduce((a, b) => a union b)
        case Distinct(args) => args.map(functionsIn).reduce((a, b) => a union b)
        case Implication(p, q) => functionsIn(p) union functionsIn(q)
        case Iff(p, q) => functionsIn(p) union functionsIn(q)
        case Eq(l, r) => functionsIn(l) union functionsIn(r)
        case App(fname, args) => args.map(functionsIn).reduce((a, b) => a union b) + fname
        case BuiltinApp(function, args) => args.map(functionsIn).reduce((a, b) => a union b)
        case Forall(vars, body) => functionsIn(body)
        case Exists(vars, body) => functionsIn(body)
    }
    def constantsIn(term: Term): Set[String] = {
        def recur(t: Term, variables: Set[String]): Set[String] = t match {
            case Top | Bottom | DomainElement(_, _) | EnumValue(_)
                | IntegerLiteral(_) | BitVectorLiteral(_, _) => Set.empty
            case Var(x) if (! (variables contains x)) => Set(x)
            case Var(x) => Set.empty
            case Not(p) => recur(p, variables)
            case AndList(args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case OrList(args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case Distinct(args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case Implication(p, q) => recur(p, variables) union recur(q, variables)
            case Iff(p, q) => recur(p, variables) union recur(q, variables)
            case Eq(l, r) => recur(l, variables) union recur(r, variables)
            case App(fname, args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case BuiltinApp(function, args) => args.map(arg => recur(arg, variables)).reduce((a, b) => a union b)
            case Forall(vars, body) => recur(body, variables ++ vars.map(_.name))
            case Exists(vars, body) => recur(body, variables ++ vars.map(_.name))
        }
        recur(term, Set.empty)
    }
}
