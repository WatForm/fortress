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

    def iflift(term:Term): Term = removeItes(liftItes(term))

    // pull all ites up as much as possible
    // functions have to be relifted through args
    def liftItes(term: Term): Term = {
        //println("liftItes in: "+term)
        val x:Term = term match {
        case Top | Bottom | Var(_) |  DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
             => term
        // for all the logical operators just push iflifting down
        case AndList(args) => AndList(args.map(liftItes))
        case OrList(args) => OrList(args.map(liftItes))
        // distinct can be over terms so turn them in not equals
        case (distinct: Distinct) => liftItes(distinct.asPairwiseNotEquals)
        case Implication(p, q) => Implication(liftItes(p), liftItes(q))
        case Iff(p, q) => Iff(liftItes(p), liftItes(q))
        case Forall(vars, body) => Forall(vars, liftItes(body))
        case Exists(vars, body) => Exists(vars, liftItes(body))
        case Not(p) => Not(liftItes(p)) 

        case IfThenElse(condition, ifTrue, ifFalse) => 
            IfThenElse(liftItes(condition),liftItes(ifTrue),liftItes(ifFalse))

        case Eq(a,b) => reLiftItes(Eq(liftItes(a),liftItes(b)))
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
    // but we can't assume they are always Boolean
    // but if they aren't Boolean they should be at the top

    def removeItes(term:Term): Term =
        term match {
        case Top | Bottom | Var(_) |  DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
             => term
        // for all the logical operators just push iflifting down
        case AndList(args) => AndList(args.map(removeItes))
        case OrList(args) => OrList(args.map(removeItes))
        case (distinct: Distinct) => Errors.Internal.preconditionFailed(s"Should not reach this 'distinct' case in removeItes: ${term}")
        case Implication(p, q) => Implication(removeItes(p), removeItes(q))
        case Iff(p, q) => Iff(removeItes(p), removeItes(q))
        case Forall(vars, body) => Forall(vars, removeItes(body))
        case Exists(vars, body) => Exists(vars, removeItes(body))
        case Not(p) => Not(removeItes(p)) 
        // only interesting case
        case IfThenElse(condition, ifTrue, ifFalse) => 
            OrList(
                AndList(removeItes(condition), removeItes(ifTrue)),
                AndList(Not(removeItes(condition)),removeItes(ifFalse))
            )
        case Eq(a,b) => Eq(removeItes(a),removeItes(b))
        case App(fname, args) => App(fname,args.map(removeItes))
        case BuiltinApp(fname,args) => BuiltinApp(fname,args.map(removeItes))
        case Closure(fname, arg1, arg2, args) => 
            Closure(fname, removeItes(arg1), removeItes(arg2),args.map(removeItes))
        case ReflexiveClosure(fname, arg1, arg2, args) => 
            ReflexiveClosure(fname, removeItes(arg1), removeItes(arg2),args.map(removeItes))
        }
}