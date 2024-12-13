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
            case Closure(f, arg1, arg2, args) => Closure(f, naturalRecur(arg1), naturalRecur(arg2), args map naturalRecur)
            case ReflexiveClosure(f, arg1, arg2, args) => ReflexiveClosure(f, naturalRecur(arg1), naturalRecur(arg2), args map naturalRecur)
            case Exists(vars, body) => Exists(vars, naturalRecur(body))
            case Forall(vars, body) => Forall(vars, naturalRecur(body))
            case IfThenElse(condition, ifTrue, ifFalse) =>
                IfThenElse(naturalRecur(condition), naturalRecur(ifTrue), naturalRecur(ifFalse))
        }
}

/**
  * Recurse through each node of the AST, calling mapTerm on each of them and replacing the AST node with the result.
  * Recursion is bottom-up.
  */
trait NaturalEachTermBottomUpRecursion extends NaturalTermRecursion {
    def mapTerm(term: Term): Term

    override val exceptionalMappings: PartialFunction[Term, Term] = PartialFunction.empty
    override def naturalRecur(term: Term): Term = mapTerm(super.naturalRecur(term))
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
            case Closure(_, arg1, arg2, args) => naturalRecur(arg1) union naturalRecur(arg2) union (args map naturalRecur reduce (_ union _))
            case ReflexiveClosure(_, arg1, arg2, args) => naturalRecur(arg1) union naturalRecur(arg2) union (args map naturalRecur reduce (_ union _))
            case Exists(vars, body) => naturalRecur(body)
            case Forall(vars, body) => naturalRecur(body)
            case IfThenElse(condition, ifTrue, ifFalse) => naturalRecur(condition) union naturalRecur(ifTrue) union naturalRecur(ifFalse)
        }
}

/**
  * Helper trait for implementing any recursive reduction over the AST.
  */
abstract class NaturalReduction[R](val identity: R, val op: (R, R) => R) {
    val exceptionalMappings: PartialFunction[Term, R]

    def naturalRecur(term: Term): R =
        if (exceptionalMappings isDefinedAt term) exceptionalMappings(term)
        else term match {
            case leaf: LeafTerm => identity
            case Not(p) => naturalRecur(p)
            case AndList(args) => (args map naturalRecur) reduce (op(_, _))
            case OrList(args) => (args map naturalRecur) reduce (op(_, _))
            case Distinct(args) => (args map naturalRecur) reduce (op(_, _))
            case Implication(l, r) => op(naturalRecur(l), naturalRecur(r))
            case Iff(l, r) => op(naturalRecur(l), naturalRecur(r))
            case Eq(l, r) => op(naturalRecur(l), naturalRecur(r))
            case App(f, args) => (args map naturalRecur) reduce (op(_, _))
            case BuiltinApp(function, args) => (args map naturalRecur) reduce (op(_, _))
            case Closure(_, arg1, arg2, args) => op(op(naturalRecur(arg1), naturalRecur(arg2)), args map naturalRecur reduce (op(_, _)))
            case ReflexiveClosure(_, arg1, arg2, args) => op(op(naturalRecur(arg1), naturalRecur(arg2)), args map naturalRecur reduce (op(_, _)))
            case Exists(vars, body) => naturalRecur(body)
            case Forall(vars, body) => naturalRecur(body)
            case IfThenElse(condition, ifTrue, ifFalse) => op(op(naturalRecur(condition), naturalRecur(ifTrue)), naturalRecur(ifFalse))
        }
}
