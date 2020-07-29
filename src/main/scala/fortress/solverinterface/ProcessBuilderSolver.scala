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

abstract class ProcessBuilderSolver extends SolverSession {
    private var processSession: Option[ProcessSession] = None
    private val convertedBytes: CharArrayWriter = new CharArrayWriter
    private var theory: Option[Theory] = None
    
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

    override def solution: Interpretation = {
        Errors.verify(processSession.nonEmpty, "Cannot get instance without a live process")

        val fortressNameToSmtValue: Map[String, String] = getFortressNameToSmtValueMap(theory.get)
        
        val smtValueToDomainElement: Map[String, DomainElement] = (
            for {
                (name, value) <- fortressNameToSmtValue
                domainElement <- DomainElement.interpretName(name)
            } yield (value -> domainElement)
        ).toMap
        
        object Solution extends EvaluationBasedInterpretation(theory.get.signature) {
            override protected def evaluateConstant(c: AnnotatedVar): Value = {
                smtValueToFortressValue(
                    fortressNameToSmtValue(c.name),
                    c.sort,
                    smtValueToDomainElement
                )
            }
            
            override protected def evaluateFunction(f: FuncDecl, argList: Seq[Value]): Value = {
                processSession.get.write("(get-value ((")
                processSession.get.write(f.name)
                for(arg <- argList){
                    processSession.get.write(" ")
                    processSession.get.write(arg.toString)
                }
                processSession.get.write(")))")
                processSession.get.write("\n")
                processSession.get.flush()
                
                val str = processSession.get.readLine()
                val value = str match {
                    case ProcessBuilderSolver.smt2Model(name, value) => value
                    case _ => Errors.unreachable()
                }
                smtValueToFortressValue(value, f.resultSort, smtValueToDomainElement)
            }
            
            override protected def evaluateSort(sort: Sort): Seq[Value] = {
                smtValueToDomainElement.values.filter(
                    domainElement => domainElement.sort == sort
                ).toIndexedSeq
            }
        }
        Solution
    }
    
    private def getFortressNameToSmtValueMap(theory: Theory): Map[String, String] = {
        for(constant <- theory.constants){
            processSession.get.write("(get-value (")
            processSession.get.write(constant.name)
            processSession.get.write("))")
        }
        processSession.get.write("\n")
        processSession.get.flush()
        
        (for(constant <- theory.constants) yield {
            val str = processSession.get.readLine()
            str match {
                case ProcessBuilderSolver.smt2Model(name, value) => {
                    Errors.verify(constant.name == name, s""""${constant.name}" should be equal to "$name"""")
                    (constant.name -> value)
                }
                case _ => Errors.unreachable()
            }
        }).toMap
    }
    
    private def smtValueToFortressValue(
        value: String,
        sort: Sort,
        smtValueToDomainElement: Map[String, DomainElement]
    ): Value = {
            
        sort match {
            case SortConst(_) => smtValueToDomainElement(value)
            case BoolSort => value match {
                case "true" => Top
                case "false" => Bottom
                case _ => Errors.unreachable()
            }
            case IntSort => IntegerLiteral(value.toInt)
            case BitVectorSort(bitwidth) => value match {
                case ProcessBuilderSolver.bitVecLiteral(radix, digits) => radix match {
                    case "x" => BitVectorLiteral(Integer.parseInt(digits, 16), bitwidth)
                    case "b" => BitVectorLiteral(Integer.parseInt(digits, 2),  bitwidth)
                    case _ => Errors.unreachable()
                }
                case ProcessBuilderSolver.bitVecExpr(digits, bitw) => {
                    Errors.verify(bitw.toInt == bitwidth)
                    BitVectorLiteral(digits.toInt, bitwidth)
                }
                case _ => Errors.unreachable()
            }
        }
    }
    
    @throws(classOf[java.io.IOException])
    override def close(): Unit = {
        processSession.foreach(_.close())
    }
    
    protected override def finalize(): Unit = close()
    
    protected def processArgs: Seq[String]
    protected def timeoutArg(timeoutMillis: Milliseconds): String
}

object ProcessBuilderSolver {
    private val smt2Model: Regex = """^\(\((\S+|\(.+\)) (\S+|\(.+\))\)\)$""".r
    private val bitVecLiteral: Regex = """^#(.)(.+)$""".r
    private val bitVecExpr: Regex = """\(_ bv(\d+) (\d+)\)""".r
}

class CVC4CliSolver extends ProcessBuilderSolver {
    def processArgs: Seq[String] = Seq("cvc4", "--lang=smt2.6", "-im")
    
    def timeoutArg(timeoutMillis: Milliseconds): String = "--tlimit-per=" + timeoutMillis.value
}

class Z3CliSolver extends ProcessBuilderSolver {
    def processArgs: Seq[String] = Seq("z3", "-smt2", "-in")
    
    def timeoutArg(timeoutMillis: Milliseconds): String = "-t:" + timeoutMillis.value
}
