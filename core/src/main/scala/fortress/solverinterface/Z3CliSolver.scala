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

//class Z3CliSolver extends StandardProcessBuilderSolver with ProcessSmtlibEvaluation {
//    def processArgs: Seq[String] = Seq("z3", "-smt2", "-in")
//
//    def timeoutArg(timeoutMillis: Milliseconds): String = "-t:" + timeoutMillis.value
//}

//class Z3IncCliSolver extends IncrementalProcessBuilderSolver with ProcessSmtlibEvaluation  {
//    def processArgs: Seq[String] = Seq("z3", "-smt2", "-in")
//}

class Z3CliSolver extends StandardProcessBuilderSolver with ProcessSmtlibParser {
    def processArgs: Seq[String] = Seq("z3", "-smt2", "-in")

    def timeoutArg(timeoutMillis: Milliseconds): String = "-t:" + timeoutMillis.value
}

class Z3IncCliSolver extends IncrementalProcessBuilderSolver with ProcessSmtlibParser  {
    def processArgs: Seq[String] = Seq("z3", "-smt2", "-in")
}