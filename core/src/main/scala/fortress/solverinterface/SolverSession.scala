package fortress.solverinterface

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._

import java.lang.AutoCloseable

/** An interactive session with some kind of external solver (e.g. a command-line SMT solver). */

//TODO Memory out errors
trait SolverSession extends AutoCloseable {
    
    // No event loggers, lower level
    def setTheory(theory: Theory): Unit
    def setScope(scope: Map[Sort, Scope]): Unit
    def addAxiom(axiom: Term): Unit
    def solve(timeoutMillis: Milliseconds): ModelFinderResult
    def solution: Interpretation
    
    @throws(classOf[java.io.IOException])
    override def close(): Unit
}
