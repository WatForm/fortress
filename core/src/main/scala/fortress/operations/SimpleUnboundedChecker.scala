package fortress.operations

import fortress.msfol._

import scala.annotation.tailrec

object SimpleUnboundedChecker {
    /*
        visit a Term, return all sorts that are
        quantified or have transitive closure applied to them
     */
    def getBoundedSort(termSeq: Seq[Term]): Set[Sort] = {
        var sortSet: Set[Sort] = Set.empty
        termSeq.foreach( term => { sortSet = sortSet ++ getBoundedSort(term) } )
        sortSet
    }

    def getBoundedSort(term: Term): Set[Sort] = term match {
        case AndList(args) => getBoundedSort(args)
        case OrList(args) => getBoundedSort(args)
        case (distinct: Distinct) => getBoundedSort(distinct.asPairwiseNotEquals)
        case Implication(p, q) => getBoundedSort(p) ++ getBoundedSort(q)
        case Iff(p, q) => getBoundedSort(p) ++ getBoundedSort(q)
        case Forall( vars, body ) => getBoundedSort(body) ++ vars.map(_.sort).toSet
        case Exists( vars, body ) => getBoundedSort(body)
        case Not(Not(p)) => getBoundedSort(p)
        case Not(AndList(args)) => getBoundedSort(args)
        case Not(OrList(args)) => getBoundedSort(args)
        case Not(distinct @ Distinct(_)) => getBoundedSort(distinct.asPairwiseNotEquals)
        case Not(Iff(p, q)) => getBoundedSort(p) ++ getBoundedSort(q)
        case Not(Forall(vars, body)) => getBoundedSort(body) ++ vars.map(_.sort).toSet
        case Not(Exists(vars, body)) => getBoundedSort(body) ++ vars.map(_.sort).toSet
        case App(f, args) => getBoundedSort(args)
        case Not(App(f, args)) => getBoundedSort(args)

        case Closure(f, arg1, arg2) => getBoundedSort(arg1) ++ getBoundedSort(arg2)
        case Not(Closure(f, arg1, arg2)) => getBoundedSort(arg1) ++ getBoundedSort(arg2)
        case ReflexiveClosure(f, arg1, arg2) => getBoundedSort(arg1) ++ getBoundedSort(arg2)
        case Not(ReflexiveClosure(f, arg1, arg2)) => getBoundedSort(arg1) ++ getBoundedSort(arg2)

        case Eq(l, r) => getBoundedSort(l) ++ getBoundedSort(r)
        case Not(Eq(l, r)) => getBoundedSort(l) ++ getBoundedSort(r)

        case IfThenElse(condition, ifTrue, ifFalse) => getBoundedSort(condition) ++ getBoundedSort(ifTrue) ++ getBoundedSort(ifFalse)

        case _ => Set.empty
    }
}
