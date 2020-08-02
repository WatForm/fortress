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

trait StandardProcessBuilderSolver extends ProcessBuilderSolver {

    private val convertedBytes: CharArrayWriter = new CharArrayWriter

    override def setTheory(theory: Theory): Unit = {
        this.theory = Some(theory)
        convertedBytes.reset()
        convertedBytes.write("(set-option :produce-models true)\n")
        convertedBytes.write("(set-logic ALL)\n")
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeTheory(theory)
    }
    
    override def solve(timeoutMillis: Milliseconds): ModelFinderResult = {
        processSession.foreach(_.close())
        processSession = Some(new ProcessSession( { processArgs :+ timeoutArg(timeoutMillis) }.asJava))
        convertedBytes.writeTo(processSession.get.inputWriter)
        processSession.get.write("(check-sat)\n")
        processSession.get.flush()
        
        // processSession.get.write(s"(set-option :timeout ${timeoutMillis.value})") // Doesn't work for CVC4
        
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
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeAssertion(axiom)
    }
}
