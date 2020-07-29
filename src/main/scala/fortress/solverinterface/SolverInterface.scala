package fortress.solverinterface

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._

trait SolverInterface {
    def openSession(): SolverSession
}

object SolverInterface {
    // For use with fortress-tests
    def makeByName(name: String): Option[SolverInterface] = name match {
        case "Z3Api" => Some(Z3ApiInterface)
        case "Z3Cli" => Some(Z3CliInterface)
        case "CVC4Cli" => Some(CVC4CliInterface)
        case _ => None
    }
}

case object Z3ApiInterface extends SolverInterface {
    def openSession(): SolverSession = new Z3ApiSolver
}

case object Z3CliInterface extends SolverInterface {
    def openSession(): SolverSession = new Z3CliSolver
}

case object CVC4CliInterface extends SolverInterface {
    def openSession(): SolverSession = new CVC4CliSolver
}
