package fortress.operations

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors

object NormalForms {
    /** Returns the negation normal form of a term. 
      * It is assumed that Eq is not used on sort Bool and so uses of Eq are atomic.
      * Additionally it is assumed that applications and arguments to applications
      * are atomic. 
      *
      * Side Effect: eliminates Implication, Iff, Distinct
      * */
    def nnf(term: Term): Term = term match {

        case Top | Bottom => term
        case Not(Top) => Bottom
        case Not(Bottom) => Top

        case Not(Not(p)) => nnf(p)

        case AndList(args) => AndList(args.map(nnf))
        case Not(AndList(args)) => OrList(args.map(arg => nnf(Not(arg))))

        case OrList(args) => OrList(args.map(nnf))
        case Not(OrList(args)) => AndList(args.map(arg => nnf(Not(arg))))

        case Implication(p, q) => OrList(nnf(Not(p)), nnf(q))
        case Not(Implication(p, q)) => AndList(nnf(p), nnf(Not(q)))

        case Iff(p, q) => OrList(
            AndList(nnf(p), nnf(q)),
            AndList(nnf(Not(p)), nnf(Not(q)))
        )
        case Not(Iff(p, q)) => OrList(
            AndList(nnf(p), nnf(Not(q))),
            AndList(nnf((Not(p))), nnf(q))
        )

        case Forall(vars, body) => Forall(vars, nnf(body))
        case Not(Forall(vars, body)) => Exists(vars, nnf(Not(body)))

        case Exists(vars, body) => Exists(vars, nnf(body))
        case Not(Exists(vars, body)) => Forall(vars, nnf(Not(body)))

        case Forall2ndOrder(declarations, body) => Forall2ndOrder(declarations, nnf(body))
        case Not(Forall2ndOrder(declarations, body)) => Exists2ndOrder(declarations, nnf(Not(body)))

        case Exists2ndOrder(declarations, body) => Exists2ndOrder(declarations, nnf(body))
        case Not(Exists2ndOrder(declarations, body)) => Forall2ndOrder(declarations, nnf(Not(body)))

        case (distinct: Distinct) => nnf(distinct.asPairwiseNotEquals)
        case Not(distinct @ Distinct(_)) => nnf(Not(distinct.asPairwiseNotEquals))

        // We do not eliminate ITEs here: see IfLifting. ITE elim is hard because the return type might not be boolean.
        // However, to enable miniscoping + anti-prenexing + partial prenexing to operate within ITEs, we recurse into
        // the ITE subformulas too. Note that this means the return value is NOT fully in NNF because the ITE condition
        // appears both negated and unnegated when ITEs are eliminated.
        case IfThenElse(condition, ifTrue, ifFalse) =>
            IfThenElse(nnf(condition), nnf(ifTrue), nnf(ifFalse))
        case Not(IfThenElse(condition, ifTrue, ifFalse)) =>
            IfThenElse(nnf(condition), nnf(Not(ifTrue)), nnf(Not(ifFalse)))

        /* nnf makes no changes to term types below this line */

        case App(fname, args) => term
        case Not(App(fname, args)) => term

        case BuiltinApp(fname, args) => term
        case Not(BuiltinApp(fname, args)) => term

        case Closure(fname, arg1, arg2, args) => term
        case Not(Closure(fname, arg1, arg2, args)) => term

        case ReflexiveClosure(fname, arg1, arg2, args) => term
        case Not(ReflexiveClosure(fname, arg1, arg2, args)) => term
        
        case SetCardinality(fname) => term

        case Eq(l, r) => term
        case Not(Eq(l, r)) => term // Note that Eq does not compare booleans

        case Var(_) | Not(Var(_)) | DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
             => term
        case Not(DomainElement(_, _))
            | Not(IntegerLiteral(_)) |  Not(BitVectorLiteral(_, _)) | Not(EnumValue(_))
            => Errors.Internal.preconditionFailed(s"Term is not well-sorted: ${term}")


    }

    // precondition: NNF
    // Note: we recurse through ITEs but do not push quantifiers through them.
    // TODO: freeVarsConstSymbols doesn't cache, so there may be many tree traversals here. This could be a bottleneck.
    private object Miniscoping extends NaturalTermRecursion {
        override val exceptionalMappings: PartialFunction[Term, Term] = {
            // Push forall through conjunctions and exists through disjunctions always
            case Forall(vars, AndList(args)) => AndList(args map { arg => naturalRecur(Forall(vars, arg)) })
            case Exists(vars, OrList(args)) => OrList(args map { arg => naturalRecur(Exists(vars, arg)) })

            // Push forall through disjunctions and exists through conjunctions when possible
            // This is valid since Fortress sorts cannot be empty
            case Forall(vars, OrList(args)) =>
                val (hasLast, hasntLast) = args.partition(arg => arg.freeVarConstSymbols contains vars.last.variable)
                if (hasntLast.isEmpty) Forall(vars, naturalRecur(OrList(args))) // max depth, move on
                else {
                    // push it in and recurse
                    val body = if (hasLast.isEmpty) Or.smart(hasntLast)
                    else Or.smart(hasntLast :+ Forall(vars.last, Or.smart(hasLast)))
                    naturalRecur(
                        if (vars.init.isEmpty) body
                        else Forall(vars.init, body)
                    )
                }
            case Exists(vars, AndList(args)) =>
                val (hasLast, hasntLast) = args.partition(arg => arg.freeVarConstSymbols contains vars.last.variable)
                if (hasntLast.isEmpty) Exists(vars, naturalRecur(AndList(args))) // max depth, move on
                else {
                    // push it in and recurse
                    val body = if (hasLast.isEmpty) And.smart(hasntLast)
                    else And.smart(hasntLast :+ Exists(vars.last, And.smart(hasLast)))
                    naturalRecur(
                        if (vars.init.isEmpty) body
                        else Exists(vars.init, body)
                    )
                }

            // Push forall(exists) and exists(forall) in again after recursion if possible
            case Forall(vars, exists @ Exists(_, _)) =>
                val body = naturalRecur(exists)
                body match {
                    case Exists(_, _) => Forall(vars, body) // it's still an exists, can't push in
                    case _ => naturalRecur(Forall(vars, body)) // try to push in
                }
            case Exists(vars, forall @ Forall(_, _)) =>
                val body = naturalRecur(forall)
                body match {
                    case Forall(_, _) => Exists(vars, body) // it's still a forall, can't push in
                    case _ => naturalRecur(Exists(vars, body)) // try to push in
                }

            // Merge nested foralls/exists
            case Forall(vars1, Forall(vars2, body)) => naturalRecur(Forall(vars1 ++ vars2, body))
            case Exists(vars1, Exists(vars2, body)) => naturalRecur(Exists(vars1 ++ vars2, body))

            // Eliminate quantifiers where the quantified variable doesn't appear in the term
            case f @ Forall(vars, _: LeafTerm | Not(_) | Eq(_, _) | App(_, _) | BuiltinApp(_, _)
                              | Closure(_, _, _, _) | ReflexiveClosure(_, _, _, _) | IfThenElse(_, _, _)) =>
                val freeVars = f.body.freeVarConstSymbols
                val remainingVars = vars.filter(freeVars contains _.variable)
                if (remainingVars.isEmpty) naturalRecur(f.body)
                else Forall(remainingVars, naturalRecur(f.body))
            case e @ Exists(vars, _: LeafTerm | Not(_) | Eq(_, _) | App(_, _) | BuiltinApp(_, _)
                              | Closure(_, _, _, _) | ReflexiveClosure(_, _, _, _) | IfThenElse(_, _, _)) =>
                val freeVars = e.body.freeVarConstSymbols
                val remainingVars = vars.filter(freeVars contains _.variable)
                if (remainingVars.isEmpty) naturalRecur(e.body)
                else Exists(remainingVars, naturalRecur(e.body))

            // Error on things we don't support: implication, iff, distinct should be eliminated
            case Implication(_, _) | Iff(_, _) | Distinct(_) =>
                Errors.Internal.preconditionFailed("Miniscoping requires NNF (implications, iff, distinct eliminated)")
        }
    }

    /** Performs miniscoping on the term. This pushes quantifiers inwards as far as possible without reordering them.
      * See Lampert (https://doi.org/10.1093/jigpal/jzx003) section 2 "Purification".
      * Precondition: term is in NNF.
      */
    def miniscope(term: Term): Term = Miniscoping.naturalRecur(term)

    // precondition: no name conflicts between quantified variables - run MaxAlphaRenaming
    // bring foralls up through disjunctions and exists up through conjunctions
    private object PartialPrenex extends NaturalTermRecursion {
        override val exceptionalMappings: PartialFunction[Term, Term] = {
            case OrList(args) =>
                val newArgs = args map naturalRecur // recurse bottom-up
                val (foralls: Seq[Forall], others: Seq[Term]) = newArgs partition { _.isInstanceOf[Forall] }
                if (foralls.isEmpty) Or.smart(newArgs)
                else {
                    val allVars = foralls.flatMap(_.vars)
                    Errors.Internal.assertion(allVars.map(_.name).distinct.size == allVars.size,
                        "PartialPrenex requires all quantified variables to have distinct names!")
                    Forall(allVars, Or.smart(foralls.map(_.body) ++ others))
                }
            case AndList(args) =>
                val newArgs = args map naturalRecur // recurse bottom-up
                val (exists: Seq[Exists], others: Seq[Term]) = newArgs partition { _.isInstanceOf[Exists] }
                if (exists.isEmpty) And.smart(newArgs)
                else {
                    val allVars = exists.flatMap(_.vars)
                    Errors.Internal.assertion(allVars.map(_.name).distinct.size == allVars.size,
                        "PartialPrenex requires all quantified variables to have distinct names!")
                    Exists(allVars, And.smart(exists.map(_.body) ++ others))
                }

            // Ensure nested foralls/exists are merged - otherwise we might miss some in the previous steps
            case Forall(vars, body) => naturalRecur(body) match {
                case Forall(subVars, subBody) => Forall(vars ++ subVars, subBody)
                case newBody => Forall(vars, newBody)
            }
            case Exists(vars, body) => naturalRecur(body) match {
                case Exists(subVars, subBody) => Exists(vars ++ subVars, subBody)
                case newBody => Exists(vars, newBody)
            }
        }
    }

    /** Move foralls upwards through disjunctions and exists upwards through conjunctions, merging.
      * E.g.: forall x. (forall y. p) & (forall z. q) --> forall x, y, z. p & q
      * See Lampert (https://doi.org/10.1093/jigpal/jzx003) section 2 "Purification".
      * Precondition: term is in NNF and all quantified variables have distinct names (MaxAlphaRenaming is run).
      * For best results, run miniscoping first.
      */
    def partialPrenex(term: Term): Term = PartialPrenex.naturalRecur(term)

    // merge nested AndLists, OrLists, Forall, Exists
    private object MergeNested extends NaturalTermRecursion {
        override val exceptionalMappings: PartialFunction[Term, Term] = {
            case AndList(args) => AndList(conjuncts(args) map naturalRecur)
            case OrList(args) => OrList(disjuncts(args) map naturalRecur)
            case Forall(vars1, Forall(vars2, body)) => naturalRecur(Forall(vars1 ++ vars2, body))
            case Exists(vars1, Exists(vars2, body)) => naturalRecur(Exists(vars1 ++ vars2, body))
        }

        private def conjuncts(args: Seq[Term]): Seq[Term] = args flatMap {
            case AndList(subArgs) => conjuncts(subArgs)
            case term => Seq(term)
        }

        private def disjuncts(args: Seq[Term]): Seq[Term] = args flatMap {
            case OrList(subArgs) => disjuncts(subArgs)
            case term => Seq(term)
        }
    }

    // quantifier sorting from Lampert
    // preconditions: nested ands/ors and foralls/exists merged, no Forall
    private object QuantifierSorting extends NaturalTermRecursion {
        override val exceptionalMappings: PartialFunction[Term, Term] = {
            case Forall(vars, OrList(disjuncts)) =>
                Forall(sortVars(vars, disjuncts), OrList(disjuncts map naturalRecur))
            case Exists(vars, AndList(conjuncts)) =>
                Exists(sortVars(vars, conjuncts), AndList(conjuncts map naturalRecur))
        }

        private def sortVars(vars: Seq[AnnotatedVar], args: Seq[Term]): Seq[AnnotatedVar] = {
            // Sort vars by decreasing number of args in which the variable appears
            val freeVarsList = args map { _.freeVarConstSymbols }
            val counts = vars.map { annVar => annVar -> freeVarsList.count(_.contains(annVar.variable)) }.toMap
            vars.sortBy(counts)(Ordering[Int].reverse)
        }
    }

    private def sortQuantifiers(term: Term): Term = QuantifierSorting.naturalRecur(MergeNested.naturalRecur(term))

    /** Anti-prenex normal form: push quantifiers inwards as far as possible, rearranging quantifiers to minimize the
      * size of the quantified formulas.
      * See Lampert (https://doi.org/10.1093/jigpal/jzx003) section 2 "Purification".
      * Precondition: term is in NNF and all quantified variables have distinct names (MaxAlphaRenaming is run).
      */
    def antiPrenex(term: Term): Term = {
        // Procedure from Lampert section 2 "Purification", minus the CNF/DNF conversion (costly)
        var result = term
        result = miniscope(result)
        result = partialPrenex(result)
        result = sortQuantifiers(result)
        result = miniscope(result)
        result
    }

}