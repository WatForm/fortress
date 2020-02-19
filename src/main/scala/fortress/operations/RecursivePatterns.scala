package fortress.operations

import fortress.msfol._

trait NaturalTermRecursion {
    val exceptionalMappings: PartialFunction[Term, Term]
    
    def naturalRecur(term: Term): Term = 
        if (exceptionalMappings isDefinedAt term) exceptionalMappings(term)
        else term match {
            case leaf: LeafTerm => term
            case Not(p) => Not(naturalRecur(p))
            case AndList(args) => AndList(args map naturalRecur)
            case OrList(args) => OrList(args map naturalRecur)
            case Distinct(args) => Distinct(args map naturalRecur)
            case Implication(l, r) => Implication(naturalRecur(l), naturalRecur(r))
            case Iff(l, r) => Iff(naturalRecur(l), naturalRecur(r))
            case Eq(l, r) => Eq(naturalRecur(l), naturalRecur(r))
            case App(f, args) => App(f, args map naturalRecur)
            case BuiltinApp(function, args) => BuiltinApp(function, args map naturalRecur)
            case Exists(vars, body) => Exists(vars, naturalRecur(body))
            case Forall(vars, body) => Forall(vars, naturalRecur(body))
    }
}

/** Helper trait for implementing recursive accumulation of sets.
  * Currently it only produces the empty set, but if you override the exceptionalMappings
  * you can customize the output. */
trait NaturalSetAccumulation[A] {
    val exceptionalMappings: PartialFunction[Term, Set[A]]
    
    def naturalRecur(term: Term): Set[A] =
        if (exceptionalMappings isDefinedAt term) exceptionalMappings(term)
        else term match {
            case leaf: LeafTerm => Set.empty
            case Not(p) => naturalRecur(p)
            case AndList(args) => (args map naturalRecur) reduce (_ union _)
            case OrList(args) => (args map naturalRecur) reduce (_ union _)
            case Distinct(args) => (args map naturalRecur) reduce (_ union _)
            case Implication(l, r) => naturalRecur(l) union naturalRecur(r)
            case Iff(l, r) => naturalRecur(l) union naturalRecur(r)
            case Eq(l, r) => naturalRecur(l) union naturalRecur(r)
            case App(f, args) => (args map naturalRecur) reduce (_ union _)
            case BuiltinApp(function, args) => (args map naturalRecur) reduce (_ union _)
            case Exists(vars, body) => naturalRecur(body)
            case Forall(vars, body) => naturalRecur(body)
        }
}
