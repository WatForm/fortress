package fortress.solverinterface

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._

trait SolverInterface {
    def openSession(): SolverSession
}

object Z3ApiInterface extends SolverInterface {
    def openSession(): SolverSession = new Z3ApiSolver
}

object Z3CliInterface extends SolverInterface {
    def openSession(): SolverSession = new Z3CliSolver
}

object CVC4CliInterface extends SolverInterface {
    def openSession(): SolverSession = new CVC4CliSolver
}
