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

class CVC4CliSolver extends StandardProcessBuilderSolver with ProcessSmtlibEvaluation {
    def processArgs: Seq[String] = Seq("cvc4", "--lang=smt2.6", "-im")
    
    def timeoutArg(timeoutMillis: Milliseconds): String = "--tlimit-per=" + timeoutMillis.value
}