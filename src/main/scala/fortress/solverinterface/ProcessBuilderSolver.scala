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
    private var process: Option[Process] = None
    private var pin: Option[BufferedWriter] = None
    private var pout: Option[BufferedReader] = None
    private var convertedBytes = new CharArrayWriter
    private var timeout = Milliseconds(60000)
    
    override def convertTheory(theory: Theory): Unit = {
        convertedBytes.reset
        
        convertedBytes write "(set-option :produce-models true)\n"
        convertedBytes write "(set-logic ALL)\n"
        val converter = new SmtlibConverter(convertedBytes)
        converter writeTheory theory
    }
    
    override def updateTimeout(remainingMillis: Milliseconds): Unit = {
        timeout = remainingMillis
    }
    
    override def runSolver: ModelFinderResult = {
        tryIO(() => {
            clearProcess
            startProcess
            convertedBytes writeTo pin.get
            checkSat
        })
    }
    
    override def logSMT2Output(eventLoggers: Seq[EventLogger]): Unit = {
        val smt2Output = convertedBytes.toString
        
        for(logger <- eventLoggers) logger.smt2Output(smt2Output)
    }
    
    private def checkSat: ModelFinderResult = {
        pin.get write "(check-sat)\n"
        
        pin.get.flush
        
        var result = pout.get.readLine
        result match {
            case "sat" => ModelFinderResult.Sat
            case "unsat" => ModelFinderResult.Unsat
            case _ => ModelFinderResult.Unknown
        }
    }
    
    override def addAxiom(axiom: Term, timeoutMillis: Milliseconds): ModelFinderResult = {
        Errors.verify(process.nonEmpty, "Cannot add axiom without a live process")
        tryIO(() => {
            val converter = new SmtlibConverter(pin.get)
            converter writeAssertion axiom
            
            checkSat
        })
    }

    override def getInstance(theory: Theory): Interpretation = {
        Errors.verify(process.nonEmpty, "Cannot get instance without a live process")

        val fortressNameToSmtValue: Map[String, String] = getFortressNameToSmtValueMap(theory)
        
        val smtValueToDomainElement: Map[String, DomainElement] = (
            for {
                (name, value) <- fortressNameToSmtValue
                domainElement <- DomainElement.interpretName(name)
            } yield (value, domainElement)
        ).toMap
        
        val sortInterpretations: Map[Sort, IndexedSeq[Value]] =
            getSortInterpretations(theory, smtValueToDomainElement)
        
        val constantInterpretations: Map[AnnotatedVar, Value] =
            getConstantInterpretations(theory, fortressNameToSmtValue, smtValueToDomainElement)
            
        val functionArgs: Map[FuncDecl, CartesianSeqProduct[Value]] =
            (for(funcDecl <- theory.functionDeclarations) yield {
                (funcDecl, new CartesianSeqProduct[Value](
                    funcDecl.argSorts
                    .map(sort => sortInterpretations(sort))
                    .toIndexedSeq))
            }).toMap
        
        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] =
            getFunctionInterpretations(theory, functionArgs, smtValueToDomainElement)
        
        new BasicInterpretation(sortInterpretations,constantInterpretations,functionInterpretations)
    }
    
    private def getFortressNameToSmtValueMap(theory: Theory): Map[String, String] = {
        for(constant <- theory.constants){
            pin.get write "(get-value ("
            pin.get write constant.name
            pin.get write "))"
        }
        pin.get write "\n"
        pin.get.flush
        
        (for(constant <- theory.constants) yield {
            val str = pout.get.readLine
            str match {
                case ProcessBuilderSolver.smt2Model(name, value) => {
                    Errors.verify(constant.name == name, s""""${constant.name}" should be equal to "$name"""")
                    (constant.name -> value)
                }
                case _ => Errors.unreachable
            }
        }).toMap
    }
    
    private def getFunctionInterpretations(
        theory: Theory,
        functionArgs: Map[FuncDecl, CartesianSeqProduct[Value]],
        smtValueToDomainElement: Map[String, DomainElement]
    ) : Map[FuncDecl, Map[Seq[Value], Value]] = {
            
        for(funcDecl <- theory.functionDeclarations;
            args <- functionArgs(funcDecl)){
                pin.get write "(get-value (("
                pin.get write funcDecl.name
                for(arg <- args){
                    pin.get write " "
                    pin.get write arg.toString
                }
                pin.get write ")))"
            }
            
        pin.get write "\n"
        pin.get.flush
            
        (for(funcDecl <- theory.functionDeclarations) yield {
            (funcDecl, (for(args <- functionArgs(funcDecl)) yield {
                val str = pout.get.readLine
                val value = str match {
                    case ProcessBuilderSolver.smt2Model(name, value) => value
                    case _ => Errors.unreachable
                }
                (args, smtValueToFortressValue(value, funcDecl.resultSort, smtValueToDomainElement))
            }).toMap)
        }).toMap
    }
    
    private def getConstantInterpretations(
        theory: Theory,
        fortressNameToSmtValue: Map[String, String],
        smtValueToDomainElement: Map[String, DomainElement]
    ) : Map[AnnotatedVar, Value] = {
            
        (for(constant <- theory.constants) yield {
            (constant,
            smtValueToFortressValue(
                fortressNameToSmtValue(constant.getName),
                constant.sort,
                smtValueToDomainElement)
            )
        }).toMap
    }
    
    private def getSortInterpretations(
        theory: Theory,
        smtValueToDomainElement: Map[String, DomainElement]): Map[Sort, IndexedSeq[Value]] = {
            
        (for(sort <- theory.sorts if !sort.isBuiltin) yield sort match{
            case SortConst(name) => (sort,
                smtValueToDomainElement.values.filter(
                    domainElement => domainElement.sort == sort
                ).toIndexedSeq)
            case _ => Errors.unreachable
        }).toMap
    }
    
    private def smtValueToFortressValue(
        value: String,
        sort: Sort,
        smtValueToDomainElement: Map[String, DomainElement]) : Value = {
            
        sort match {
            case SortConst(_) => smtValueToDomainElement(value)
            case BoolSort => value match {
                case "true" => Top
                case "false" => Bottom
                case _ => Errors.unreachable
            }
            case IntSort => IntegerLiteral(value.toInt)
            case BitVectorSort(bitwidth) => value match {
                case ProcessBuilderSolver.bitVecLiteral(radix, digits) => radix match {
                    case "x" => BitVectorLiteral(Integer.parseInt(digits, 16), bitwidth)
                    case "b" => BitVectorLiteral(Integer.parseInt(digits, 2),  bitwidth)
                    case _ => Errors.unreachable
                }
                case ProcessBuilderSolver.bitVecExpr(digits, bitw) => {
                    Errors.verify(bitw.toInt == bitwidth)
                    BitVectorLiteral(digits.toInt, bitwidth)
                }
                case _ => Errors.unreachable
            }
        }
    }
    
    private def tryIO(func: () => ModelFinderResult): ModelFinderResult = {
        try {
            func()
        } catch {
            case ex: IOException => {
                clearProcess
                ModelFinderResult.Error
            }
        }
    }
    
    private def startProcess: Unit = {
        process = Some(new ProcessBuilder(processArgs).start())
        pin = Some(new BufferedWriter(new OutputStreamWriter(process.get.getOutputStream)))
        pout = Some(new BufferedReader(new InputStreamReader(process.get.getInputStream)))
    }
    
    private def clearProcess: Unit = {
        finalize
        pin = None
        pout = None
        process = None
    }
    
    override protected def finalize: Unit = {
        if(process.nonEmpty) {
            pin.get.close
            pout.get.close
            process.get.destroy
        }
    }
    
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
