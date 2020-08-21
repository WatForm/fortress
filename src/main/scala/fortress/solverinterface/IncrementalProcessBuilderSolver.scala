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

trait IncrementalProcessBuilderSolver extends ProcessBuilderSolver {

    override def setTheory(theory: Theory): Unit = {
        // Convert theory
        this.theory = Some(theory)
        val convertedBytes = new CharArrayWriter
        convertedBytes.reset()
        convertedBytes.write("(set-option :produce-models true)\n")
        convertedBytes.write("(set-logic ALL)\n")
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeTheory(theory)

        // Write theory to process
        processSession.foreach(_.close())
        processSession = Some(new ProcessSession(processArgs.asJava))
        convertedBytes.writeTo(processSession.get.inputWriter)
    }
    
    override def solve(timeoutMillis: Milliseconds): ModelFinderResult = {
        processSession.get.write(s"(set-option :timeout ${timeoutMillis.value})") // Doesn't work for CVC4
        processSession.get.write("(check-sat)\n")
        processSession.get.flush()
        
        val result = processSession.get.readLine()
        result match {
            case "sat" => ModelFinderResult.Sat
            case "unsat" => ModelFinderResult.Unsat
            case "unknown" => {
                processSession.get.write("(get-info :reason-unknown)\n")
                processSession.get.flush()

                val reason = processSession.get.readLine()

                if(reason.contains("timeout"))
                    ModelFinderResult.Timeout
                else
                    ModelFinderResult.Unknown
            }
            case _ => ErrorResult(s"Unrecognized result '${result}'" )
        }
    }
    
    override def addAxiom(axiom: Term): Unit = {
        Errors.verify(processSession.nonEmpty, "Cannot add axiom without a live process")
        val convertedBytes: CharArrayWriter = new CharArrayWriter
        convertedBytes.reset()
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeAssertion(axiom)
        convertedBytes.writeTo(processSession.get.inputWriter)
    }

    protected def processArgs: Seq[String]
}