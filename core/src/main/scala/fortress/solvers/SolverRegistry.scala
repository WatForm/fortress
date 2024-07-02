package fortress.solvers


object SolverRegistry {

    def fromString(str: String): Option[Solver] = {
        str.toLowerCase() match {
            case "CVC4CliSolver" => Some(new CVC4CliSolver)
            case "Z3NonIncCliSolver" => Some(new Z3NonIncCliSolver)
            case _ => None
        }
    }

}