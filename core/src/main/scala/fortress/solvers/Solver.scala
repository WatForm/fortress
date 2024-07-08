package fortress.solvers

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfinders._
import fortress.util._

abstract class Solver extends AutoCloseable {

    def setTheory(theory: Theory): Unit
    def addAxiom(axiom: Term): Unit
    def solve(timeoutMillis: Milliseconds): ModelFinderResult
    def solution: Interpretation

    @throws(classOf[java.io.IOException])
    override def close(): Unit

    // do not overwrite in a subclass
    def name = StringHelpers.chopOff(this.getClass.getSimpleName,"Solver")
}
