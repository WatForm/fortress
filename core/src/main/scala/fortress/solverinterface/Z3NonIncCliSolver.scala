package fortress.solverinterface

import fortress.util._

class Z3NonIncCliSolver extends SMTLIBCliSolver {
    override def processArgs: Seq[String] = Seq("z3", "-smt2", "-in")

    override def timeoutArg(timeoutMillis: Milliseconds): String = "-t:" + timeoutMillis.value
}