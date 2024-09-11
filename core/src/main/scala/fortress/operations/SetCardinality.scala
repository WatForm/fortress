package fortress.operations

import fortress.msfol._

object SetCardinality {

    def cardinality(term: Term): Term = term match {
        // case SetCardinality(p) => term
        // here we make definitions based on p
        // we because we found a set cardinality, we know we definitions for inP and cardP
        // bc cardP = Findp(all elements in A)
        // Findp = ite(inA(a), 1, 0)
        //is this the only case that matters?
        // or does this represent #(#something) which wouldn't make much sense

        case Top | Bottom => term
        case Not(Top) => term
        case Not(Bottom) => term

        // is the count of True == 1?

        case Not(Not(p)) => term

        case AndList(args) => term
        // #(x| x > 3 ^ y | y < 2) == #(x | x > 3) + #(y | y < 2)
        // is that true?? I kind of don't think so
        // note PLUS not AND

        case Not(AndList(args)) => term

        case OrList(args) => AndList(args.map(cardinality))
        // #(x| x > 3 v y | y < 2) == #(x | x > 3) + #(y | y < 2)


        case Not(OrList(args)) => term

        case Implication(p, q) => term
        // is this the same as the number of a => b such that a and b are true?


        case Not(Implication(p, q)) => term

        case Iff(p, q) => term

        case Not(Iff(p, q)) => term

        case Forall(vars, body) => term
        case Not(Forall(vars, body)) => term

        case Exists(vars, body) => term
        case Not(Exists(vars, body)) => term

        case (distinct: Distinct) => term
        case Not(distinct @ Distinct(_)) => term

        case IfThenElse(condition, ifTrue, ifFalse) => term
        case Not(IfThenElse(condition, ifTrue, ifFalse)) => term

        case App(fname, args) => term
        // it looks like this might be out goal term, app being a predicate
        // a predicate is a special kind of App with a boolean return
        // can be of any arity but it must return a bool


        case Not(App(fname, args)) => term

        case BuiltinApp(fname, args) => term
        case Not(BuiltinApp(fname, args)) => term

        case Closure(fname, arg1, arg2, args) => term
        case Not(Closure(fname, arg1, arg2, args)) => term

        case ReflexiveClosure(fname, arg1, arg2, args) => term
        case Not(ReflexiveClosure(fname, arg1, arg2, args)) => term

        case Eq(l, r) => term
        case Not(Eq(l, r)) => term

        case Var(_) | Not(Var(_)) | DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
             => term
        case Not(DomainElement(_, _))
            | Not(IntegerLiteral(_)) |  Not(BitVectorLiteral(_, _)) | Not(EnumValue(_))
            => term
    }

//     // we potentially want something like this?
//     // def getFixedSorts(fname: String): Seq[Sort] = signature.queryFunction(fname) match {
//     //     case None => Errors.Internal.impossibleState("Function " + fname + " does not exist in signature when closing over it!")
//     //     case Some(Left(FuncDecl(_, sorts, _))) => sorts.drop(2).toList
//     //     case Some(Right(FunctionDefinition(_, params, _, _))) => params.map(_.sort).drop(2).toList
//     // }

//     // def ite(term: Term): Term {
//     //     return IfThenElse(term, 1, 0)
//     // }

//     // def removeCardinality(term: Term): Term{
//     //     term match {
//     //         case SetCardinality(term) => SumList (
//     //             ite(term) for term in something
//     //         )
//     //         case _ => term

//     //     }
//     // }
}