package fortress.operations

import fortress.msfol._

object ScopeSubtype {

    def subtypePred(sort: Sort): String = s"__@Pred_${sort}"

    def addBoundsPredicates(term: Term, helpMap: Map[String, Boolean]): Term = term match {
        case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => term
        case Not(p) => Not(addBoundsPredicates(p, helpMap))
        case AndList(args) => AndList(args.map(addBoundsPredicates(_, helpMap)))
        case OrList(args) => OrList(args.map(addBoundsPredicates(_, helpMap)))
        case Distinct(args) => Distinct(args.map(addBoundsPredicates(_, helpMap)))
        case Implication(l, r) => Implication(addBoundsPredicates(l, helpMap), addBoundsPredicates(r, helpMap))
        case Iff(l, r) => Iff(addBoundsPredicates(l, helpMap), addBoundsPredicates(r, helpMap))
        case Eq(l, r) => Eq(addBoundsPredicates(l, helpMap), addBoundsPredicates(r, helpMap))
        case App(f, args) => App(f, args.map(addBoundsPredicates(_, helpMap)))
        case BuiltinApp(function, arguments) => BuiltinApp(function, arguments.map(addBoundsPredicates(_, helpMap)))
        case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(addBoundsPredicates(condition, helpMap), addBoundsPredicates(ifTrue, helpMap), addBoundsPredicates(ifFalse, helpMap))
        case Exists(vars, body) => {
            val predApps = for {
                av <- vars if !av.sort.isBuiltin && !helpMap(av.sort.name)
            } yield App(subtypePred(av.sort), av.variable)
            Exists(vars, And.smart(predApps :+ addBoundsPredicates(body, helpMap)))
        }
        case Forall(vars, body) => {
            val predApps = for {
                av <- vars if !av.sort.isBuiltin && !helpMap(av.sort.name)
            } yield App(subtypePred(av.sort), av.variable)
            Forall(vars, Implication(And.smart(predApps), addBoundsPredicates(body, helpMap)))
        }
    }
}
