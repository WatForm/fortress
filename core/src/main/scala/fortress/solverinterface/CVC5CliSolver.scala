package fortress.solverinterface

import fortress.util._


class CVC5CliSolver extends Z3NonIncSolver {
    override def processArgs: Seq[String] = Seq("cvc5", "--lang=smt2.6", "-im")
    
    override def timeoutArg(timeoutMillis: Milliseconds): String = "--tlimit-per=" + timeoutMillis.value
}