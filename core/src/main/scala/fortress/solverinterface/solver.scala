package fortress.solverinterface

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._

trait solver extends AutoCloseable {
    def setTheory(theory: Theory): Unit
    def addAxiom(axiom: Term): Unit
    def solve(timeoutMillis: Milliseconds): ModelFinderResult
    def solution: Interpretation
    def unsatCore: String

    @throws(classOf[java.io.IOException])
    override def close(): Unit
}
