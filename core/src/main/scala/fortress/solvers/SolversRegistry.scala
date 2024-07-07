package fortress.solvers


object SolversRegistry {

    def fromString(str: String): Option[Solver] = {
        str match {
            case "CVC4CliSolver" => Some(new CVC4CliSolver)
            case "Z3NonIncCliSolver" => Some(new Z3NonIncCliSolver)
            case _ => None
        }
    }

}