package fortress.solverinterface

import fortress.modelfind.{ErrorResult, ModelFinderResult}
import fortress.util._
import fortress.msfol._
import fortress.operations._

import java.io.CharArrayWriter


/*
    Non-Incremental solving:
        close current process and open a new one every time,
        write theory from buffer to z3 process and call check-sat only once in one process.
 */

class Z3NonIncSolver extends SMTLIBCLISession {
    def processArgs: Seq[String] = Seq("z3", "-smt2", "-in")

    def timeoutArg(timeoutMillis: Milliseconds): String = "-t:" + timeoutMillis.value

    private val convertedBytes: CharArrayWriter = new CharArrayWriter

    override def setTheory(theory: Theory): Unit = {
        this.theory = Some(theory)
        convertedBytes.reset()
        convertedBytes.write("(set-option :produce-models true)\n")
        convertedBytes.write("(set-logic ALL)\n")
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeTheory(theory)
    }

    override def addAxiom(axiom: Term): Unit = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot add axiom without a live process")
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeAssertion(axiom)
    }

    override def solve(timeoutMillis: Milliseconds): ModelFinderResult = {
        processSession.foreach(_.close())
        processSession = Some(new ProcessSession( { processArgs :+ timeoutArg(timeoutMillis) }.asJava))
        convertedBytes.writeTo(processSession.get.inputWriter)
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


}
