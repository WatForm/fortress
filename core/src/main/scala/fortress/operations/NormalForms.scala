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

        case (distinct: Distinct) => nnf(distinct.asPairwiseNotEquals)
        case Not(distinct @ Distinct(_)) => nnf(Not(distinct.asPairwiseNotEquals))

        /* nnf makes no changes to term types below this line */

        case IfThenElse(condition, ifTrue, ifFalse) => term
        case Not(IfThenElse(condition, ifTrue, ifFalse)) => term

        case App(fname, args) => term
        case Not(App(fname, args)) => term

        case BuiltinApp(fname, args) => term
        case Not(BuiltinApp(fname, args)) => term

        case Closure(fname, arg1, arg2, args) => term
        case Not(Closure(fname, arg1, arg2, args)) => term

        case ReflexiveClosure(fname, arg1, arg2, args) => term
        case Not(ReflexiveClosure(fname, arg1, arg2, args)) => term

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
    // TODO maybe lots of tree traversals due to lack of caching with freeVarsConstSymbols
    // TODO what to do about ITEs? currently we ignore them, are they eliminated?
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
                    val body = Or.smart(hasntLast :+ Forall(vars.last, Or.smart(hasLast)))
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
                    val body = And.smart(hasntLast :+ Exists(vars.last, And.smart(hasLast)))
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
                              | Closure(_, _, _, _) | ReflexiveClosure(_, _, _, _) | IfThenElse(_, _, _))
                if (f.body.freeVarConstSymbols intersect vars.map(_.variable).toSet).isEmpty =>
                val remainingVars = vars.filter(f.body.freeVarConstSymbols contains _.variable)
                if (remainingVars.isEmpty) f.body
                else Forall(remainingVars, f.body)
            case e @ Exists(vars, _: LeafTerm | Not(_) | Eq(_, _) | App(_, _) | BuiltinApp(_, _)
                              | Closure(_, _, _, _) | ReflexiveClosure(_, _, _, _) | IfThenElse(_, _, _))
                if (e.body.freeVarConstSymbols intersect vars.map(_.variable).toSet).isEmpty =>
                val remainingVars = vars.filter(e.body.freeVarConstSymbols contains _.variable)
                if (remainingVars.isEmpty) e.body
                else Exists(remainingVars, e.body)

            // Error on things we don't support: implication, iff, distinct should be eliminated
            case Implication(_, _) | Iff(_, _) | Distinct(_) =>
                Errors.Internal.preconditionFailed("Miniscoping requires NNF (implications, iff, distinct eliminated)")
        }
    }

    // expects term to be in NNF
    // TODO: the sorting from Lampert for more complete anti-prenexing
    def antiPrenex(term: Term): Term = Miniscoping.naturalRecur(term)

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

    // pull up foralls through conjunctions and exists through disjunctions
    def partialPrenex(term: Term): Term = PartialPrenex.naturalRecur(term)

}