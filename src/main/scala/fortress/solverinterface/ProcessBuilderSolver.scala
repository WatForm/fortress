package fortress.solverinterface

import java.io._

import fortress.data.CartesianSeqProduct
import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._
import fortress.solverinterface._
import fortress.operations.SmtlibConverter

import scala.util.matching.Regex

abstract class ProcessBuilderSolver extends SolverTemplate {
    private var processSession: Option[ProcessSession] = None
    private var convertedBytes = new CharArrayWriter
    private var timeout = Milliseconds(60000)
    
    override def convertTheory(theory: Theory): Unit = {
        // Just writes the theory to the char array buffer
        convertedBytes.reset()
        
        convertedBytes.write("(set-option :produce-models true)\n")
        convertedBytes.write("(set-logic ALL)\n")
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeTheory(theory)
    }
    
    override def updateTimeout(remainingMillis: Milliseconds): Unit = {
        timeout = remainingMillis
    }
    
    override def runSolver: ModelFinderResult = {
        tryIO {
            openSession()
            convertedBytes.writeTo(processSession.get.inputWriter)
            checkSat
        }
    }
    
    override def logSMT2Output(eventLoggers: Seq[EventLogger]): Unit = {
        val smt2Output = convertedBytes.toString
        
        for(logger <- eventLoggers) logger.smt2Output(smt2Output)
    }
    
    private def checkSat: ModelFinderResult = {
        processSession.get.write("(check-sat)\n")
        processSession.get.flush()
        
        var result = processSession.get.readLine()
        result match {
            case "sat" => ModelFinderResult.Sat
            case "unsat" => ModelFinderResult.Unsat
            case "unknown" => {
                processSession.get.write("(get-info :reason-unknown)\n")
                processSession.get.flush()

                var reason = processSession.get.readLine()

                if(reason.contains("timeout"))
                    ModelFinderResult.Timeout
                else
                    ModelFinderResult.Unknown
            }
            case _ => ModelFinderResult.Error
        }
    }
    
    override def addAxiom(axiom: Term, timeoutMillis: Milliseconds): ModelFinderResult = {
        Errors.verify(processSession.nonEmpty, "Cannot add axiom without a live process")
        tryIO {
            val converter = new SmtlibConverter(processSession.get.inputWriter)
            converter.writeAssertion(axiom)
            
            checkSat
        }
    }

    override def getInstance(theory: Theory): Interpretation = {
        Errors.verify(processSession.nonEmpty, "Cannot get instance without a live process")

        val fortressNameToSmtValue: Map[String, String] = getFortressNameToSmtValueMap(theory)
        
        val smtValueToDomainElement: Map[String, DomainElement] = (
            for {
                (name, value) <- fortressNameToSmtValue
                domainElement <- DomainElement.interpretName(name)
            } yield (value -> domainElement)
        ).toMap
        
        object Solution extends EvaluationBasedInterpretation(theory.signature) {
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
    
    private def tryIO(func: => ModelFinderResult): ModelFinderResult = {
        try {
            func
        } catch {
            case ex: IOException => {
                close()
                ModelFinderResult.Error
            }
        }
    }
    
    private def openSession(): Unit = {
        processSession = Some(new ProcessSession(processArgs))
    }
    
    @throws(classOf[java.io.IOException])
    override def close(): Unit = processSession.get.close()
    
    protected override def finalize(): Unit = close()
    
    protected def timeoutMillis: Milliseconds = timeout
    
    protected def processArgs: java.util.List[String]
}

object ProcessBuilderSolver {
    private val smt2Model: Regex = """^\(\((\S+|\(.+\)) (\S+|\(.+\))\)\)$""".r
    private val bitVecLiteral: Regex = """^#(.)(.+)$""".r
    private val bitVecExpr: Regex = """\(_ bv(\d+) (\d+)\)""".r
}

class CVC4CliSolver extends ProcessBuilderSolver {
    def processArgs: java.util.List[String] = {
        java.util.List.of("cvc4", "--lang=smt2.6", "-im", "--tlimit-per=" + timeoutMillis.value)
    }
}

class Z3CliSolver extends ProcessBuilderSolver {
    def processArgs: java.util.List[String] = {
        java.util.List.of("z3", "-smt2", "-in", "-t:" + timeoutMillis.value)
    }
}
