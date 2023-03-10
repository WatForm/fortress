package fortress.operations

import fortress.msfol._
import fortress.problemstate._
import fortress.interpretation._

class MergeMonotonicSorts(monoSorts: Set[Sort]) {
    val mono: Sort = SortConst("MONO")

    def replaceSort(sort: Sort): Sort = if (monoSorts contains sort) mono else sort

    def replaceMonotonicSorts(term: Term): Term = term match {
        case Forall(args, body) => {
            val newArgs: Seq[AnnotatedVar] = for (arg <- args) yield AnnotatedVar(arg.variable, replaceSort(arg.sort))
            Forall(newArgs, replaceMonotonicSorts(body))
        }
        case Exists(args, body) => {
            val newArgs: Seq[AnnotatedVar] = for (arg <- args) yield AnnotatedVar(arg.variable, replaceSort(arg.sort))
            Exists(newArgs, replaceMonotonicSorts(body))
        }
        case Implication(p, q) => Implication(replaceMonotonicSorts(p), replaceMonotonicSorts(q))
        case Iff(p, q) => Iff(replaceMonotonicSorts(p), replaceMonotonicSorts(q))
        case IfThenElse(a, b, c) => IfThenElse(replaceMonotonicSorts(a), replaceMonotonicSorts(b), replaceMonotonicSorts(c))
        case App(f, args) => App(f, args.map(replaceMonotonicSorts))
        case Not(body) => Not(replaceMonotonicSorts(body))
        case AndList(args) => AndList(args.map(replaceMonotonicSorts))
        case OrList(args) => OrList(args.map(replaceMonotonicSorts))
        case Eq(l, r) => Eq(replaceMonotonicSorts(l), replaceMonotonicSorts(r))
        case Closure(fname, arg1, arg2, args) => Closure(fname, replaceMonotonicSorts(arg1), replaceMonotonicSorts(arg2), args.map(replaceMonotonicSorts))
        case ReflexiveClosure(fname, arg1, arg2, args) => ReflexiveClosure(fname, replaceMonotonicSorts(arg1), replaceMonotonicSorts(arg2), args.map(replaceMonotonicSorts))
        case DomainElement(index, sort) => DomainElement(index, replaceSort(sort)) //***//
        case _ => term
    }

    def updateFuncDecls(fds: Set[FuncDecl]): Set[FuncDecl] = {
        for(f <- fds) yield {
            val args: Seq[Sort] = f.argSorts.map(replaceSort)
            val result: Sort = replaceSort(f.resultSort)
            FuncDecl(f.name, args, result)
        }
    }

    def updateFuncDefs(fds: Set[FunctionDefinition]): Set[FunctionDefinition] = {
        for(f <- fds) yield {
            val args: Seq[AnnotatedVar] = for (arg <- f.argSortedVar) yield AnnotatedVar(arg.variable, replaceSort(arg.sort))
            val result: Sort = replaceSort(f.resultSort)
            FunctionDefinition(f.name, args, result, f.body)
        }
    }

    def updateConstants(constants: Set[AnnotatedVar]): Set[AnnotatedVar] =
        for (c <- constants) yield AnnotatedVar(c.variable, replaceSort(c.sort))

    def updateAxioms(axioms: Set[Term]): Set[Term] = axioms.map(replaceMonotonicSorts)

    def updateScopes(scopes: Map[Sort, Scope], exactScopeForMONO: Boolean): Map[Sort, Scope] = {
        val monoScopes: Map[Sort, Scope] = scopes.filter(s => monoSorts.contains(s._1))
        val maxSizeOfMonoSorts: Int = monoScopes.maxBy(_._2.size)._2.size
        val nonMonoScopes: Map[Sort, Scope] = scopes.filterNot(s => monoSorts.contains(s._1))
        nonMonoScopes + (mono -> (if(exactScopeForMONO) ExactScope(maxSizeOfMonoSorts) else NonExactScope(maxSizeOfMonoSorts)))
    }

    def updateRangeRestrictions(rangeRestricts: Set[RangeRestriction]): Set[RangeRestriction] = {
        for(r <- rangeRestricts) yield {
            val t: Term = replaceMonotonicSorts(r.term)
            val values: Seq[DomainElement] = for (d <- r.values) yield DomainElement(d.index, replaceSort(d.sort))
            RangeRestriction(t, values)
        }
    }

    def updateTheory(theory: Theory): Theory = {
        val nonMonoSorts: Set[Sort] = theory.sorts -- monoSorts
        val newSignature: Signature = Signature(
            nonMonoSorts + mono,
            updateFuncDecls(theory.functionDeclarations),
            updateFuncDefs(theory.functionDefinitions),
            updateConstants(theory.constants),
            theory.enumConstants
        )
        val newAxioms: Set[Term] = updateAxioms(theory.axioms)
        Theory(newSignature, newAxioms)
    }
}
