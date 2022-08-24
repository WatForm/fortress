package fortress.solverinterface

import java.io._

import fortress.data.CartesianSeqProduct
import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._
import fortress.solverinterface._
import fortress.operations.PythonZ3Converter

import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

trait Z3PythonProcessBuilderSolver extends ProcessBuilderSolver {

    private val convertedBytes: CharArrayWriter = new CharArrayWriter

    override def setTheory(theory: Theory): Unit = {
        this.theory = Some(theory)
        convertedBytes.reset()
        // Setup
        // TODO should this be outside of this?
        convertedBytes.write("from z3 import *\n")
        // use converter to write the theory definition
        val converter = new PythonZ3Converter(convertedBytes)
        converter.writeTheory(theory)
    }

    override def addAxiom(axiom: Term): Unit = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot add axiom without a live process")
        val converter = new PythonZ3Converter(convertedBytes)
        converter.writeAssertion(axiom)
    }

    override def solve(timeoutMillis: Milliseconds): ModelFinderResult = {
        processSession.foreach(_.close())
        // TODO fix this!!!
        //processSession = Some(new ProcessSession({ processArgs :+ timeoutArg(timeoutMillis) }.asJava))
        processSession = Some(new ProcessSession({processArgs}.asJava))
        convertedBytes.writeTo(processSession.get.inputWriter)
        processSession.get.write("__solver.check()\n")
        processSession.get.flush()

        val resultStr = processSession.get.readLine()
        resultStr match {
            case "sat" => ModelFinderResult.Sat
            case "unsat" => ModelFinderResult.Unsat
            // NOTE We cannot timeout in python directly
            // we could make some construct around this to handle this case
            case "unknown" => ModelFinderResult.Unknown
            case _ => ErrorResult(s"Unrecognized result '${resultStr}'" )
        }
    }

    override def solution: Interpretation = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot get instance without a live process")

        object Solution extends Interpretation {
            override def constantInterpretations: Map[AnnotatedVar,Value] = Map()
            override def functionInterpretations: Map[FuncDecl,Map[Seq[Value],Value]] = Map()
            override def sortInterpretations: Map[Sort,Seq[Value]] = Map()
        }
        Solution
    }

    protected def processArgs: Seq[String]
    protected def timeoutArg(timeoutMillis: Milliseconds): String
}