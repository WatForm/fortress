// need some sort of equivalent to
// case IfThenElse(condition, ifTrue, ifFalse) =>
//             OrList(
//                 AndList(removeItesForBoolTerm(condition), removeItesForBoolTerm(ifTrue)),
//                 AndList(Not(removeItesForBoolTerm(condition)),removeItesForBoolTerm(ifFalse))
//             )

// first step - need to caputure in the language when cardinality occurs

// BOOKMARK, UNFINISHED
// what is the SomePredicateStatement?
// these are operations in the ast that take a thing in the ast and return a thing also in said ast !!
case SetCardinality(SomePredicateStatement){
    total = 0; // not really, we want total to be the sequence of statements
    For x in Universe:
        total += IfThenElse(SomePredicateStatement(x), 1, 0)
    return total; // except we don't want to return the count, we want to return the predicate logic REPRESENTING the count
    // the TERM does the counting, not the code

    // returning the plus, not the actual count

    // the SORT of what we are returning is an integer
    // the CODE of what we are returning is the TERM that has said sort
}


// think match and case statements

//


// The general idea for this operation is we started with
// # (Term)
// and we want to return the equivalent sum of ite statements
// # (Term) turns into ife(term(x1), 0, 1) + ife(term(x1), 0, 1)
// in this example the Scope of term would be {x1, x2}
// important to remember we're just trying to return another term!!

// set cardinality takes a PREDICATE, as in

// Predicates in SE212 - a symbol representing an attribute of a property or the meaning of a relationship between two or more values

// predicate that takes in one value - urany predicate, two, binary predicate

// we should assume the predicate we pass in can take in any number of arguments

// do something like def ite (...) and call ite + ite + ite to speed things up

// things like #(x) should do nothing if x isnt a predicate
// but should #(likes(x)) work??
// #g.address where groups map to addresses is valid syntax in alloy
// but what does that mean when we get to this level??

// In our case a predicate is an expression with scopes that returns true or false

object SetCardinality {
    def cardinality(term: Term): Term = term match {
        case Top | Bottom => term
        case Not(Top) => term
        case Not(Bottom) => term

        // is the count of True == 1?

        case Not(Not(p)) => term

        case AndList(args) => term
        // #(x| x > 3 ^ y | y < 2) == #(x | x > 3) + #(y | y < 2)
        // is that true?? I kind of don't think so
        // note PLUS not AND

        case Not(AndList(args)) =>

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

    // we potentially want something like this?
    def getFixedSorts(fname: String): Seq[Sort] = signature.queryFunction(fname) match {
        case None => Errors.Internal.impossibleState("Function " + fname + " does not exist in signature when closing over it!")
        case Some(Left(FuncDecl(_, sorts, _))) => sorts.drop(2).toList
        case Some(Right(FunctionDefinition(_, params, _, _))) => params.map(_.sort).drop(2).toList
    }

    def ite(term: Term): Term {
        return IfThenElse(condition, 1, 0)
    }

    def removeCardinality(){
        term match {
            case IfThenElse(condition, ifTrue, ifFalse) =>
                OrList(
                    AndList(removeItesForBoolTerm(condition), removeItesForBoolTerm(ifTrue)),
                    AndList(Not(removeItesForBoolTerm(condition)),removeItesForBoolTerm(ifFalse))
                )
            case _ => term

        }
    }
}