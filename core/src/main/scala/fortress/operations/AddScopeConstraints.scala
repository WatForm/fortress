package fortress.operations

import fortress.msfol._
import fortress.problemstate._


/*
    |A| = x
    forall a:A, f(a)  ====>  (forall a:A, f(a)) or ( |A| < x )
 */

object AddScopeConstraints {

    def getSorts(term: Term, funcDecls: Set[FuncDecl]): Set[Sort] = term match {
        case Eq(l, r) => {
            getSorts(l, funcDecls) ++ getSorts(r, funcDecls) - BoolSort
        }
        case App(f, args) => {
            val func: FuncDecl = funcDecls.filter(fd => fd.name == f).head
            var sorts: Set[Sort] = func.argSorts.toSet
            for( arg <- args) sorts = sorts ++ getSorts(arg, funcDecls)
            sorts - BoolSort
        }
        case _ => Set.empty
    }

    def addScopeConstraints(axiom: Term, clauses: Map[Sort, Seq[Term]], funcDecls: Set[FuncDecl]): Term = axiom match {
        case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_,_) |IntegerLiteral(_) | BitVectorLiteral(_, _) => axiom
        case Not(body) => Not(addScopeConstraints(body, clauses, funcDecls))
        case AndList(args) => AndList(args.map(addScopeConstraints(_, clauses, funcDecls)))
        case OrList(args) => OrList(args.map(addScopeConstraints(_, clauses, funcDecls)))
        case Distinct(args) => Distinct(args.map(addScopeConstraints(_, clauses, funcDecls)))
        case Implication(l, r) => Implication(addScopeConstraints(l, clauses, funcDecls), addScopeConstraints(r, clauses, funcDecls))
        case Iff(l, r) => Iff(addScopeConstraints(l, clauses, funcDecls), addScopeConstraints(r, clauses, funcDecls))
//        case Eq(l ,r) => Eq(addScopeConstraints(l, clauses), addScopeConstraints(r, clauses))
        case Eq(l, r) => {
            // f(a) = b  ===>  f(a) = b or |A|<x
            val sorts: Set[Sort] = getSorts(axiom, funcDecls)
            var orList: Seq[Term] = Seq(axiom)
            for(sort <- sorts) orList = orList.+:(clauses(sort).head)
            OrList(orList)
        }
        case App(f, args) => {
            val func: FuncDecl = funcDecls.filter(fd => fd.name == f).head
            if( func.resultSort == BoolSort ) {
                var orList: Seq[Term] = Seq(axiom)
                for( sort <- func.argSorts ) orList = orList.+:(clauses(sort).head)
                OrList(orList)
            }
            App(f, args.map(addScopeConstraints(_, clauses, funcDecls)))
        }
        case BuiltinApp(f, args) => BuiltinApp(f, args.map(addScopeConstraints(_, clauses, funcDecls)))
        case IfThenElse(a,b,c) => IfThenElse(addScopeConstraints(a, clauses, funcDecls), addScopeConstraints(b, clauses, funcDecls), addScopeConstraints(c, clauses, funcDecls))
        case Exists(vars, body) => Exists(vars, addScopeConstraints(body, clauses, funcDecls))

        case Forall(vars, body) => {
            println("error: there should not be forall in current axioms")
            null
        }
    }
}
