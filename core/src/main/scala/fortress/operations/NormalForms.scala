package fortress.operations

import fortress.msfol._
import fortress.util.Errors

object NormalForms {
    /** Returns the negation normal form of a term. 
      * It is assumed that Eq is not used on sort Bool and so uses of Eq are atomic.
      * Additionally it is assumed that applications and arguments to applications
      * are atomic. */
    def nnf(term: Term): Term = term match {
        case AndList(args) => AndList(args.map(nnf))
        case OrList(args) => OrList(args.map(nnf))
        case (distinct: Distinct) => nnf(distinct.asPairwiseNotEquals)
        case Implication(p, q) => OrList(nnf(Not(p)), nnf(q))
        case Iff(p, q) => OrList(
            AndList(nnf(p), nnf(q)),
            AndList(nnf(Not(p)), nnf(Not(q)))
        )
        case Forall(vars, body) => Forall(vars, nnf(body))
        case Exists(vars, body) => Exists(vars, nnf(body))
        case Not(Top) => Bottom
        case Not(Bottom) => Top
        case Not(Not(p)) => nnf(p)
        case Not(AndList(args)) => OrList(args.map(arg => nnf(Not(arg))))
        case Not(OrList(args)) => AndList(args.map(arg => nnf(Not(arg))))
        case Not(distinct @ Distinct(_)) => nnf(Not(distinct.asPairwiseNotEquals))
        case Not(Implication(p, q)) => AndList(nnf(p), nnf(Not(q)))
        case Not(Iff(p, q)) => OrList(
            AndList(nnf(p), nnf(Not(q))),
            AndList(nnf((Not(p))), nnf(q))
        )
        case Not(Forall(vars, body)) => Exists(vars, nnf(Not(body)))
        case Not(Exists(vars, body)) => Forall(vars, nnf(Not(body)))
        case App(fname, args) => App(fname, args map nnf)
        case Not(App(fname, args)) => Not(App(fname, args map nnf)) 

        case Closure(fname, args, arg1, arg2) => Closure(fname, args map nnf, nnf(arg1), nnf(arg2))
        case Not(Closure(fname, args, arg1, arg2)) => Not(Closure(fname, args map nnf, nnf(arg1), nnf(arg2)))
        case ReflexiveClosure(fname, args, arg1, arg2) => ReflexiveClosure(fname, args map nnf, nnf(arg1), nnf(arg2))
        case Not(ReflexiveClosure(fname, args, arg1, arg2)) => Not(ReflexiveClosure(fname, args map nnf, nnf(arg1), nnf(arg2)))
            
        case Eq(l, r) => Eq(nnf(l), nnf(r))
        case Not(Eq(l, r)) => Not(Eq(nnf(l), nnf(r))) // Not that Eq does not compare booleans
        case Top | Bottom | Var(_) | BuiltinApp(_, _) | DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
            | Not(Var(_)) | Not(BuiltinApp(_, _)) => term
        case Not(DomainElement(_, _)) | Not(IntegerLiteral(_))
            |  Not(BitVectorLiteral(_, _)) | Not(EnumValue(_)) => Errors.Internal.preconditionFailed(s"Term is not well-sorted: ${term}")
        case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(nnf(condition), nnf(ifTrue), nnf(ifFalse))
        case Not(IfThenElse(condition, ifTrue, ifFalse)) => Errors.Internal.preconditionFailed(s"Term is not santitized, ite cannot return Boolean: ${term}")
    }

    def prenex(term: Term): Term = ???
}