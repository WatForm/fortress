package fortress.operations

import fortress.msfol._

case class EnumValueEliminator(eliminationMapping: Map[EnumValue, DomainElement]) extends NaturalTermRecursion {
    override val exceptionalMappings: PartialFunction[Term, Term] = {
        case e @ EnumValue(_) if (eliminationMapping contains e) => eliminationMapping(e)
    }
    
    def apply(term : Term): Term = naturalRecur(term)
}

object DomainElementEliminatorConstants {
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
            case BuiltinApp(function, args) => BuiltinApp(function, args map eliminateDomainElements)
            case Closure(fname, arg1, arg2, args) => Closure(fname, eliminateDomainElements(arg1), eliminateDomainElements(arg2), args.map(eliminateDomainElements))
            case ReflexiveClosure(fname, arg1, arg2, args) => ReflexiveClosure(fname, eliminateDomainElements(arg1), eliminateDomainElements(arg2), args.map(eliminateDomainElements))
            case Exists(vars, body) => Exists(vars, eliminateDomainElements(body))
            case Forall(vars, body) => Forall(vars, eliminateDomainElements(body))
            case IfThenElse(condition, ifTrue, ifFalse) =>
                IfThenElse(eliminateDomainElements(condition), eliminateDomainElements(ifTrue), eliminateDomainElements(ifFalse))
            case Top | Bottom | Var(_) | EnumValue(_)
                | IntegerLiteral(_) | BitVectorLiteral(_, _) => term
        }
        eliminateDomainElements(term)
    }
}

object DomainElementEliminatorEnums {
    def apply(term: Term): Term = {
        def eliminateDomainElements(term: Term): Term = term match {
            case d @ DomainElement(_, _) => d.asEnumValue
            case Not(p) => Not(eliminateDomainElements(p))
            case AndList(args) => AndList(args.map(eliminateDomainElements))
            case OrList(args) => OrList(args.map(eliminateDomainElements))
            case Implication(l, r) => Implication(eliminateDomainElements(l), eliminateDomainElements(r))
            case Distinct(args) => Distinct(args.map(eliminateDomainElements))
            case Iff(l, r) => Iff(eliminateDomainElements(l), eliminateDomainElements(r))
            case Eq(l, r) => Eq(eliminateDomainElements(l), eliminateDomainElements(r))
            case App(fname, args) => App(fname, args.map(eliminateDomainElements))
            case BuiltinApp(function, args) => BuiltinApp(function, args map eliminateDomainElements)
            case Closure(fname, arg1, arg2, args) => Closure(fname, eliminateDomainElements(arg1), eliminateDomainElements(arg2), args map eliminateDomainElements)
            case ReflexiveClosure(fname, arg1, arg2, args) => ReflexiveClosure(fname, eliminateDomainElements(arg1), eliminateDomainElements(arg2), args map eliminateDomainElements)
            case Exists(vars, body) => Exists(vars, eliminateDomainElements(body))
            case Forall(vars, body) => Forall(vars, eliminateDomainElements(body))
            case IfThenElse(condition, ifTrue, ifFalse) =>
                IfThenElse(eliminateDomainElements(condition), eliminateDomainElements(ifTrue), eliminateDomainElements(ifFalse))
            case Top | Bottom | Var(_) | EnumValue(_)
                 | IntegerLiteral(_) | BitVectorLiteral(_, _) => term
        }
        eliminateDomainElements(term)
    }
}
