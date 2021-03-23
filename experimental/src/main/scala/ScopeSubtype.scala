package fortress.operations

import fortress.msfol._

object ScopeSubtype {

    def subtypePred(sort: Sort): String = s"__@Pred_${sort}"

    def addBoundsPredicates(term: Term): Term = term match {
        case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => term
        case Not(p) => Not(addBoundsPredicates(p))
        case AndList(args) => AndList(args.map(addBoundsPredicates))
        case OrList(args) => OrList(args.map(addBoundsPredicates))
        case Distinct(args) => Distinct(args.map(addBoundsPredicates))
        case Implication(l, r) => Implication(addBoundsPredicates(l), addBoundsPredicates(r))
        case Iff(l, r) => Iff(addBoundsPredicates(l), addBoundsPredicates(r))
        case Eq(l, r) => Eq(addBoundsPredicates(l), addBoundsPredicates(r))
        case App(f, args) => App(f, args.map(addBoundsPredicates))
        case BuiltinApp(function, arguments) => BuiltinApp(function, arguments.map(addBoundsPredicates))
        case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(addBoundsPredicates(condition), addBoundsPredicates(ifTrue), addBoundsPredicates(ifFalse))
        case Exists(vars, body) => {
            val predApps = for {
                av <- vars if !av.sort.isBuiltin
            } yield App(subtypePred(av.sort), av.variable)
            Exists(vars, And.smart(predApps :+ addBoundsPredicates(body)))
        }
        case Forall(vars, body) => {
            val predApps = for {
                av <- vars if !av.sort.isBuiltin
            } yield App(subtypePred(av.sort), av.variable)
            Forall(vars, Implication(And.smart(predApps), addBoundsPredicates(body)))
        }
    }
}