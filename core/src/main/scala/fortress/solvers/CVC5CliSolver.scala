package fortress.solvers

import fortress.util._

class CVC5CliSolver extends SMTLIBCliSolver {
    override def processArgs: Seq[String] = Seq("cvc5", "--lang=smt2.6", "-im")
    
    override def timeoutArg(timeoutMillis: Milliseconds): String = "--tlimit-per=" + timeoutMillis.value
}