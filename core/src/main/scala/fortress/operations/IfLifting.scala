package fortress.operations

import fortress.msfol._
import fortress.util.Errors

object IfLifter {

    /** Returns a Term with no ites
      * Cannot assume the term argument is of sort Boolean
      * so removal of ites is not always possible
      * 
      * Side Effect: distinct is also removed
      */

    def iflift(term:Term, s:Sort): Term = {
        //println("enter iflift: "+term+" "+s)
        if (s == BoolSort) return removeItesForBoolTerm(liftItes(term))
        else return liftItes(term)
}

    // pull all ites up as much as possible
    // functions have to be relifted through args
    def liftItes(term: Term): Term = {
        //println("liftItes in: "+term)
        val x:Term = term match {
        case Top | Bottom | Var(_) |  DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
             => term

        // for all the terms we know take Boolean args 
        // push iflifting down
        // and immediately removeItes
        case AndList(args) => AndList(args.map(t => removeItesForBoolTerm(liftItes(t))))
        case OrList(args) => OrList(args.map(t => removeItesForBoolTerm(liftItes(t)))) 
        case Implication(p, q) => Implication(removeItesForBoolTerm(liftItes(p)), removeItesForBoolTerm(liftItes(q)))
        case Iff(p, q) => Iff(removeItesForBoolTerm(liftItes(p)), removeItesForBoolTerm(liftItes(q)))
        case Forall(vars, body) => Forall(vars, removeItesForBoolTerm(liftItes(body)))
        case Exists(vars, body) => Exists(vars, removeItesForBoolTerm(liftItes(body)))
        case Not(p) => Not(removeItesForBoolTerm(liftItes(p))) 
        case Eq(a,b) => removeItesForBoolTerm(reLiftItes(Eq(liftItes(a),liftItes(b))))

        // distinct can be over terms so turns them in not equals
        // has to return a Boolean
        case (distinct: Distinct) => removeItesForBoolTerm(liftItes(distinct.asPairwiseNotEquals))

        // if there is an ite in these args
        // these might return an ite (possibly with a stack of ites)
        // they might not be of Boolean value
        case IfThenElse(condition, ifTrue, ifFalse) => 
            IfThenElse(removeItesForBoolTerm(liftItes(condition)),liftItes(ifTrue),liftItes(ifFalse))

        case App(fname, args) => reLiftItes(App(fname,args.map(liftItes)))
        case BuiltinApp(fname,args) => reLiftItes(BuiltinApp(fname,args.map(liftItes)))
        case Closure(fname, arg1, arg2, args) => 
            reLiftItes(Closure(fname, liftItes(arg1), liftItes(arg2),args.map(liftItes)))
        case ReflexiveClosure(fname, arg1, arg2, args) => 
            reLiftItes(ReflexiveClosure(fname, liftItes(arg1), liftItes(arg2), args.map(liftItes)))
        }
        //println("liftItes out: "+x)
        return x
    }

    // push function through a stack of ites
    // f(ite(c1,ite(c2,a,b),d),e)
    // = ite(c1,f(ite(c2,a,b),d),f(e))
    // = ite(c1,  ite(c2,f(a),f(b)), f(e))
    // can stop when no more ites to hit
    def reLiftItes(term:Term): Term = {
        //println("reLiftItes in: "+term)
        val x = term match {
        case Top | Bottom | Var(_) |  DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
             => term
        // for all the logical operators just push iflifting down
        case AndList(_) | OrList(_) | Implication(_,_) |
            Iff(_,_) | Forall(_,_) | Exists(_,_) | Not(_) => term
        case IfThenElse(_, _, _) => term 
        case (distinct: Distinct) => Errors.Internal.preconditionFailed(s"Should not reach this 'distinct' case in reLiftItes: ${term}")
        case Eq(a,b) => reLiftOverArgs((args: Seq[Term]) => Eq(args(0),args(1)), Seq(a,b))
        case App(fname, args) => reLiftOverArgs((args: Seq[Term]) => App(fname,args), args)
        case BuiltinApp(fname,args) => reLiftOverArgs((args:Seq[Term]) => BuiltinApp(fname,args), args)
        case Closure(fname, arg1, arg2, args) => 
            reLiftOverArgs(
                (args:Seq[Term]) => Closure(fname, args(0), args(1), args.slice(2, args.size -1)), 
                Seq(arg1,arg2) ++ args)
        case ReflexiveClosure(fname, arg1, arg2, args) => 
            reLiftOverArgs(
                (args:Seq[Term]) => ReflexiveClosure(fname, args(0), args(1), args.slice(2, args.size -1)), 
                Seq(arg1,arg2) ++ args)
        }
        //println("reLiftItes out: "+x)
        return x
    }
    // common functionality for reLifting to go through list of args and recombine
    // with a constructor hidden in c
    def reLiftOverArgs(c:Seq[Term] => Term,args:Seq[Term]):Term = {
        //println("reLiftOverArgs in: "+args)
        var newargs = Seq[Term]()
        for(i <- 0 to args.size-1) {
            val a = args.lift(i)
            a match {
                case Some(IfThenElse(condition, ifTrue, ifFalse)) =>
                    // could be empty if this is the last arg
                    val argsafter = args.slice(i+1, args.size)
                    //println("argsafter: "+argsafter)
                    val argsTrue = newargs ++ Seq(ifTrue) ++ argsafter
                    //println("argsTrue: "+argsTrue)
                    val argsFalse = newargs ++ Seq(ifFalse) ++ argsafter
                    //println("argsFalse: "+argsFalse)
                    // returns a value and doesn't loop any more

                    val y = IfThenElse(
                        reLiftItes(condition),
                        reLiftItes(c(argsTrue)),
                        reLiftItes(c(argsFalse))
                    )
                    //println("reLiftOverArgs out: "+y)
                    return y
                case Some(x) => {
                    // if not an ite, don't need to relift it
                    newargs = newargs ++ List(x)
                }
                case None => 
                    Errors.Internal.preconditionFailed(s"Should not reach this case in IfLifting: ${a}")
            }     
        }
        // only reaches here if there was no ite in an argument
        // all of newargs have been relifted
        //println("reLiftOverArgs out: "+c(newargs))
        return c(newargs)
    }

    // all ites are lifted to the top (although may be nested)
    // this should only be called if certain term is Boolean
    // but if they aren't Boolean they should be at the top

    def removeItesForBoolTerm(term:Term): Term =
        term match {

        // only interesting case
        case IfThenElse(condition, ifTrue, ifFalse) => 
            OrList(
                AndList(removeItesForBoolTerm(condition), removeItesForBoolTerm(ifTrue)),
                AndList(Not(removeItesForBoolTerm(condition)),removeItesForBoolTerm(ifFalse))
            )

        // ites have already been lifted out of function applications
        // Boolean/Eq operator have already had ites removed
        case _ => term

        }
}