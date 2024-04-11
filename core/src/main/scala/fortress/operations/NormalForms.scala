package fortress.operations

import fortress.msfol._
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

    def prenex(term: Term): Term = ???
}