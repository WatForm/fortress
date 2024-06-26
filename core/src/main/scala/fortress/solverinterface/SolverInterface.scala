// this is separate from solver
// so that we can pass the solver as an object to the model finder
// and the model finder can "create" a solver by using "openSession" 

package fortress.solverinterface

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._

trait SolverInterface {
    def openSession(): Solver
}

/*
object SolverInterface {
    // For use with fortress-tests
    def makeByName(name: String): Option[SolverInterface] = name match {
        case "Z3NonIncCli" => Some(Z3NonIncCliInterface)
        case "CVC4Cli" => Some(CVC4CliInterface)
        case _ => None
    }
}
*/

case object Z3NonIncCliInterface extends SolverInterface {
    def openSession(): Solver = new Z3NonIncCliSolver
}

case object CVC4CliInterface extends SolverInterface {
    def openSession(): Solver = new CVC4CliSolver
}
