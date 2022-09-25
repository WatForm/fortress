package fortress.solverinterface

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._

trait SolverInterface {
    def openSession(): solver
}

object SolverInterface {
    // For use with fortress-tests
    def makeByName(name: String): Option[SolverInterface] = name match {
        case "Z3Cli" => Some(Z3CliInterface)
        case "Z3IncCli" => Some(Z3IncCliInterface)
        case "CVC4Cli" => Some(CVC4CliInterface)
        case _ => None
    }
}

case object Z3CliInterface extends SolverInterface {
    def openSession(): solver = new Z3NonIncSolver
}

case object Z3IncCliInterface extends SolverInterface {
    def openSession(): solver = new Z3IncSolver
}

case object CVC4CliInterface extends SolverInterface {
    def openSession(): solver = new CVC4CliSolver
}
