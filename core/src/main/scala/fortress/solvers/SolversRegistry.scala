package fortress.solvers

import fortress.util.Errors 

object SolversRegistry {

    def fromString(str: String): Solver = {
       val sv:Solver = str match {
            case "CVC4CliSolver" => new CVC4CliSolver
            case "Z3NonIncCliSolver" => new Z3NonIncCliSolver
            case _ => {
                Errors.API.solverDoesNotExist(str)
                null
            }
        }
        checkName(str,sv)
    }

    private def checkName(s:String, sv:Solver):Solver = {
        Errors.Internal.assertion(sv.name == s, s +" does not match "+ sv.name)
        sv        
    }

}