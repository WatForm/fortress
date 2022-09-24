package fortress.solverinterface

import java.io._

import fortress.data.CartesianSeqProduct
import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._
import fortress.solverinterface._
import fortress.operations.SmtlibConverter

import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

/*
    Default solving mode used by fortress.
    Write axioms to one z3 process and call check-sat multiple times.
 */


class Z3IncSolver extends SMTLIBCLISession {
    def processArgs: Seq[String] = Seq("z3", "-smt2", "-in")

    def timeoutArg(timeoutMillis: Milliseconds): String = "-t:" + timeoutMillis.value
}