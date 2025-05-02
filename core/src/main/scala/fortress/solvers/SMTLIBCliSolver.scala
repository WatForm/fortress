/*
    Default solving mode used by fortress.
    All SMT CLI solvers share these functions to process the text CLI inputs and outputs
    Write axioms to one solver process and call check-sat multiple times.
 */

package fortress.solvers

import fortress.inputs._
import fortress.interpretation._
import fortress.modelfinders.{ErrorResult, ModelFinderResult}
import fortress.util._
import fortress.msfol._
import fortress.operations._

import scala.util.matching.Regex
import java.io.CharArrayWriter
import scala.jdk.CollectionConverters._
import scala.collection.mutable
import org.antlr.v4.runtime.Parser


trait SMTLIBCliSolver extends Solver {

    protected def processArgs: Seq[String]
    protected def timeoutArg(timeoutMillis: Milliseconds): String
    protected var theory: Option[Theory] = None
    
    protected var processSession: Option[ProcessSession] = None

    private val convertedBytes: CharArrayWriter = new CharArrayWriter

    @throws(classOf[java.io.IOException])
    override def close(): Unit = {
        processSession.foreach(_.close())
    }

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
        // println("Adding axiom: " + axiom)
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeAssertion(axiom)
    }

    override def solve(timeoutMillis: Milliseconds): ModelFinderResult = {
        processSession.foreach(_.close())
        // println("Opening new process session")
        processSession = Some(new ProcessSession( { processArgs :+ timeoutArg(timeoutMillis) }.asJava))
        // println("Sending to Z3:")
        // println(convertedBytes)
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

    // return a model if the theory is satisfiable, used by func viewModel
    override def solution: Interpretation = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot get instance without a live process")

        val model: String = getModel

        val solution = new ParserBasedInterpretation(model, theory.get)
        solution
    }


    // get solution in smt-lib format form solver by cmd "get-model"
    def getModel: String = {
        var model: String = ""
        processSession.get.write("(get-model)\n")
        processSession.get.flush()
        var line: String = processSession.get.readLine()
        while ({line = processSession.get.readLine(); line != ")"}) {
            model ++= line + "\n"
        }
        model
    }


}
