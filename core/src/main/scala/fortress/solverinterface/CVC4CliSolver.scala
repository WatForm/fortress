package fortress.solverinterface

import fortress.util._

class CVC4CliSolver extends SMTLIBCliSolver {
    override def processArgs: Seq[String] = Seq("cvc4", "--lang=smt2.6", "-im")
    
    override def timeoutArg(timeoutMillis: Milliseconds): String = "--tlimit-per=" + timeoutMillis.value
}