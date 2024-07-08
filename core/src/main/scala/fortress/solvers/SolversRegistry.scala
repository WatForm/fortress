package fortress.solvers

import fortress.util.Errors 

object SolversRegistry {

    def fromString(str: String): Option[Solver] = {
        str match {
            case "CVC4CliSolver" => checkMatch(str,new CVC4CliSolver)
            case "Z3NonIncCliSolver" => checkMatch(str, new Z3NonIncCliSolver)
            case _ => None
        }
    }

    private def checkMatch(s:String, sv:Solver) = {
        Errors.Internal.assertion(sv.name != s, s +"does not match"+ sv.name)
        Some(sv)        
    }

}