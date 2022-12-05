package fortress.operations

import fortress.msfol._
import fortress.problemstate._


/*
    |A| = x
    forall a:A, f(a)  ====>  (forall a:A, f(a)) or ( |A| < x )
 */

object AddScopeConstraints {

    def getSorts(term: Term, theory: Theory): Set[Sort] = term match {
        case Eq(l, r) => {
            getSorts(l, theory) ++ getSorts(r, theory) - BoolSort
        }
        case App(f, args) => {
            val func: FuncDecl = theory.functionDeclarations.filter(fd => fd.name == f).head
            var sorts: Set[Sort] = func.argSorts.toSet
            for( arg <- args) sorts = sorts ++ getSorts(arg, theory)
            sorts - BoolSort
        }
        case Var(name) => {
            for( av <- theory.signature.constants if av.name == name ) yield av.sort
        }
        case EnumValue(_) => {
            for( ev <- theory.signature.enumConstants if ev._2.contains(term)) yield ev._1
        }.toSet
        case DomainElement(index, sort) => Set(sort)
        case _ => Set.empty
    }

    def addScopeConstraints(axiom: Term, clauses: Map[Sort, Seq[Term]], theory: Theory): Term = axiom match {
        case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_,_) |IntegerLiteral(_) | BitVectorLiteral(_, _) => axiom
        case Not(body) => Not(addScopeConstraints(body, clauses, theory))
        case AndList(args) => AndList(args.map(addScopeConstraints(_, clauses, theory)))
        case OrList(args) => OrList(args.map(addScopeConstraints(_, clauses, theory)))
        case Distinct(args) => Distinct(args.map(addScopeConstraints(_, clauses, theory)))
        case Implication(l, r) => Implication(addScopeConstraints(l, clauses, theory), addScopeConstraints(r, clauses, theory))
        case Iff(l, r) => Iff(addScopeConstraints(l, clauses, theory), addScopeConstraints(r, clauses, theory))
//        case Eq(l ,r) => Eq(addScopeConstraints(l, clauses), addScopeConstraints(r, clauses))
        case Eq(l, r) => {
            // f(a) = b  ===>  f(a) = b or |A|<x
            val sorts: Set[Sort] = getSorts(axiom, theory)
            var orList: Seq[Term] = Seq(axiom)
            for(sort <- sorts) orList = orList.+:(clauses(sort).head)
            if(orList.size>=2) OrList(orList)
            else axiom
        }
        case App(f, args) => {
            val func: FuncDecl = theory.functionDeclarations.filter(fd => fd.name == f).head
            if( func.resultSort == BoolSort ) {
                var orList: Seq[Term] = Seq(axiom)
                for( sort <- func.argSorts ) orList = orList.+:(clauses(sort).head)
                OrList(orList)
            }
            App(f, args.map(addScopeConstraints(_, clauses, theory)))
        }
        case BuiltinApp(f, args) => BuiltinApp(f, args.map(addScopeConstraints(_, clauses, theory)))
        case IfThenElse(a,b,c) => IfThenElse(addScopeConstraints(a, clauses, theory), addScopeConstraints(b, clauses, theory), addScopeConstraints(c, clauses, theory))
        case Exists(vars, body) => Exists(vars, addScopeConstraints(body, clauses, theory))

        case Forall(vars, body) => {
            println("error: there should not be forall in current axioms")
            null
        }
    }
}
