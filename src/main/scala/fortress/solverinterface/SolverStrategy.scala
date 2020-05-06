package fortress.solverinterface

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._

/** An abstraction of which solving method should be used to search for a satisfying model.
* For example, dumping the theory to SMT-LIB and solving it using a command-line SMT solver. */

//TODO Memory out errors
trait SolverStrategy {
    /**
    * Attempts to solve the given theory, searching for a satisfying instance.
    */
    @throws(classOf[java.io.IOException])
    def solve(theory: Theory, timeoutMillis: Int, log: java.io.Writer): ModelFinderResult
    def addAxiom(axiom: Term, timeoutMillis: Int, log: java.io.Writer): ModelFinderResult

    def getInstance(theory: Theory): Interpretation
}
