package fortress.operations


import fortress.msfol._
import fortress.util.Errors

object IfLifter {
    /** Returns the if-lifted form of a Term
      * Assumes the term argument is of sort Boolean
      * so removal of ites is always possible
      */

    def iflift(term: Term): Term = term match {

        // App/BuiltinApp and Eq are the two interesting cases for iflifting
        case App(fname, args) => {
                var newargs = List[Term]()
                for(i <- 0 to args.size-1) {
                    val a = args.lift(i)
                    a match {
                        case Some(IfThenElse(condition, ifTrue, ifFalse)) =>
                            // could be empty if this is the last arg
                            val argsafter = args.slice(i+1, args.size -1)
                            val argsTrue = newargs ++ List(ifTrue) ++ argsafter
                            val argsFalse = newargs ++ List(ifFalse) ++ argsafter
                            // returns a value and doesn't loop any more
                            OrList(
                                AndList(
                                    iflift(condition),iflift(App(fname,argsTrue))),
                                AndList(
                                    Not(iflift(condition)),iflift(App(fname,argsFalse)))
                            )
                        case Some(x) => {
                            val newa = iflift(x)
                            newargs = newargs ++ List(newa)
                        }
                        case None => 
                            Errors.Internal.preconditionFailed(s"Should not reach this case in IfLifting: ${term}")
                    }
                    
                }
                // only reaches here if there was no ite in an argument
                // all of newargs have been iflifted
                App(fname,newargs)
        }

        // this is largely a duplication of the above
        // but it is not easy to factor it into a helper function
        case BuiltinApp(fname, args) => {
                var newargs = List[Term]()
                for(i <- 0 to args.size-1) {
                    val a = args.lift(i)
                    a match {
                        case Some(IfThenElse(condition, ifTrue, ifFalse)) =>
                            // could be empty if this is the last arg
                            val argsafter = args.slice(i+1, args.size -1)
                            val argsTrue = newargs ++ List(ifTrue) ++ argsafter
                            val argsFalse = newargs ++ List(ifFalse) ++ argsafter
                            // returns a value and doesn't loop any more
                            OrList(
                                AndList(
                                    iflift(condition),iflift(BuiltinApp(fname,argsTrue))),
                                AndList(
                                    Not(iflift(condition)),iflift(BuiltinApp(fname,argsFalse)))
                            )
                        case Some(x) => {
                            val newa = iflift(x)
                            newargs = newargs ++ List(newa)
                        }
                        case None => 
                            Errors.Internal.preconditionFailed(s"Should not reach this case in IfLifting: ${term}")
                    }
                    
                }
                // only reaches here if there was no ite in an argument
                // all of newargs have been iflifted
                BuiltinApp(fname,newargs)
        }
        case Eq(l, r) => {
            l match {
                case IfThenElse(condition,ifTrue, ifFalse) =>
                    OrList(
                        AndList(iflift(condition),iflift(Eq(ifTrue,r))),
                        AndList(Not(iflift(condition)),iflift(Eq(ifFalse,r)))
                    )
                case x =>
                    r match {
                        case IfThenElse(condition,ifTrue,ifFalse) =>
                            OrList(
                                AndList(iflift(condition),iflift(Eq(l,ifTrue))),
                                AndList(Not(iflift(condition)),iflift(Eq(l,ifFalse)))
                            )
                        case y =>
                            Eq(iflift(l),iflift(r))
                    }
            }
        }


        // for all the logical operators just push iflifting down
        case AndList(args) => AndList(args.map(iflift))
        case OrList(args) => OrList(args.map(iflift))
        case (distinct: Distinct) => iflift(distinct.asPairwiseNotEquals)
        case Implication(p, q) => OrList(iflift(Not(p)), iflift(q))
        case Iff(p, q) => OrList(
            AndList(iflift(p), iflift(q)),
            AndList(iflift(Not(p)), iflift(Not(q)))
        )
        case Forall(vars, body) => Forall(vars, iflift(body))
        case Exists(vars, body) => Exists(vars, iflift(body))
        case Not(p) => Not(iflift(p))

        // should not be any ite's in these
        // TODO: typechecking should disallow this if possible
        case Closure(fname, arg1, arg2, args) => term
        case ReflexiveClosure(fname, arg1, arg2, args) => term
            
        case Top | Bottom | Var(_) |  DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
             => term

        // should only reach this point if ite is the top-level formula
        // so ifTrue and ifFalse must be of boolean sort
        case IfThenElse(condition, ifTrue, ifFalse) => 
            OrList(
                AndList(iflift(condition),iflift(ifTrue)),
                AndList(iflift(condition),iflift(ifFalse))
            )
    }

}