package fortress.solverinterface

import fortress.tfol._
import fortress.interpretation._
import fortress.modelfind._

/** An abstraction of which solving method should be used to search for a satisfying model.
* For example, dumping the theory to SMT-LIB and solving it using a command-line SMT solver. */

//TODO Memory out errors
trait SolverStrategy {
    /** Returns true if and only if the solver can attempt to solve the given theory.
    * For example, a SolverStrategy that invokes a SAT solver will reject a theory
    * containing quantifiers, since another TheoryTransformer should be invoked to
    * map it down into propositional logic.
    * Note that just because a solver can attempt to solve a theory does not mean
    * it will succeed.
    * For example, a SolverStrategy that invokes an SMT solver may still timeout
    * or give up partway through a solving attempt if the theory is from an
    * undecidable logic.
    */
    def canAttemptSolving(theory: Theory): Boolean
    
    /**
    * Attempts to solve the given theory, searching for a satisfying instance.
    */
    @throws(classOf[java.io.IOException])
    def solve(theory: Theory, timeoutMillis: Int, log: java.io.Writer): ModelFinderResult
    
    def getInstance(theory: Theory): Interpretation
}
