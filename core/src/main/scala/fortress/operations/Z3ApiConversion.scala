package fortress.operations

import scala.util.{Try,Success,Failure}

import com.microsoft.z3;

import fortress.msfol._
import fortress.util.Errors
import fortress.util.NameConverter._

class Z3ApiConverter(ctx: z3.Context){

    def findVars(term: Term): Set[String] = {
        term match {
            // Var is it's own var
            case Var(name) => Set(name)
            // No vars in constants
            case Top | Bottom => Set()
            // Recurse
            case Not(p) => findVars(p)
            // Got an error trying to just make these alternatives to the same case. Not sure why
            // Folds to union all arguments together
            case AndList(args) => args.foldLeft[Set[String]](Set())(_ union findVars(_))
            case OrList(args) => args.foldLeft[Set[String]](Set())(_ union findVars(_))
            case Distinct(args) => args.foldLeft[Set[String]](Set())(_ union findVars(_))
            case Implication(left, right) => findVars(left) union findVars(right)
            case Iff(left, right) => findVars(left) union findVars(right)
            case Eq(left, right) => findVars(left) union findVars(right)
            case _ => Set()
        }
    }
}

