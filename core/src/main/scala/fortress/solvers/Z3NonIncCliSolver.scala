package fortress.solvers

import fortress.util._

class Z3NonIncCliSolver extends SMTLIBCliSolver {
    override def processArgs: Seq[String] = Seq("z3", "model.user_functions=false", "-smt2", "-in")

    override def timeoutArg(timeoutMillis: Milliseconds): String = "-t:" + timeoutMillis.value
}