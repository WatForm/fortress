package fortress.operations

import fortress.msfol._
import fortress.problemstate._


/*
    |A| = x
    forall a:A, f(a)  ====>  (forall a:A, f(a)) or ( |A| < x )
 */

object AddScopeConstraints {

    def addScopeConstraints(axiom: Term, clauses: Map[Sort, Seq[Term]]): Term = axiom match {
        case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_,_) |IntegerLiteral(_) | BitVectorLiteral(_, _) => axiom
        case Not(body) => Not(addScopeConstraints(body, clauses))
        case AndList(args) => AndList(args.map(addScopeConstraints(_, clauses)))
        case OrList(args) => OrList(args.map(addScopeConstraints(_, clauses)))
        case Distinct(args) => Distinct(args.map(addScopeConstraints(_, clauses)))
        case Implication(l, r) => Implication(addScopeConstraints(l, clauses), addScopeConstraints(r, clauses))
        case Iff(l, r) => Iff(addScopeConstraints(l, clauses), addScopeConstraints(r, clauses))
        case Eq(l ,r) => Eq(addScopeConstraints(l, clauses), addScopeConstraints(r, clauses))
        case App(f, args) => App(f, args.map(addScopeConstraints(_, clauses)))
        case BuiltinApp(f, args) => BuiltinApp(f, args.map(addScopeConstraints(_, clauses)))
        case IfThenElse(a,b,c) => IfThenElse(addScopeConstraints(a, clauses), addScopeConstraints(b, clauses), addScopeConstraints(c, clauses))
        case Exists(vars, body) => Exists(vars, addScopeConstraints(body, clauses))

        case Forall(vars, body) => {
            var newBody: Seq[Term] = Seq(body)
            for( av <- vars ) {
                newBody = newBody.+:(clauses(av.sort).head)
            }
            Forall(vars, Or.smart(newBody))
        }
    }
}
