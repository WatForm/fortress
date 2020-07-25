package fortress.solverinterface

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._

import java.lang.AutoCloseable

/** An abstraction of which solving method should be used to search for a satisfying model.
* For example, dumping the theory to SMT-LIB and solving it using a command-line SMT solver. */

//TODO Memory out errors
trait SolverStrategy extends AutoCloseable {
    /**
    * Attempts to solve the given theory, searching for a satisfying instance.
    */
    def solve(theory: Theory, timeoutMillis: Milliseconds, eventLoggers: Seq[EventLogger]): ModelFinderResult
    def addAxiom(axiom: Term, timeoutMillis: Milliseconds): ModelFinderResult

    def getInstance(theory: Theory): Interpretation
}
