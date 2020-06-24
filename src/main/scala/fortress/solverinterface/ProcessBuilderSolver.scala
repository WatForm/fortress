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
    
    private val smt2Model: Regex = """^\(\((.+) (.+)\)\)$""".r
    
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
        Errors.verify(process.nonEmpty, "Cannot add axiom without a live cvc4 session")
        tryIO(() => {
            val converter = new SmtlibConverter(pin.get)
            converter writeAssertion axiom
            
            checkSat
        })
    }

    override def getInstance(theory: Theory): Interpretation = {
        Errors.verify(process.nonEmpty, "Cannot get instance without a live cvc4 session")
        System.out.println("getting instance");
        System.out.println("getting instance " + theory.constants.size);
        try{
            for(constant <- theory.constants){
                pin.get write "(get-value ("
                pin.get write constant.name
                pin.get write "))"
            }
            pin.get write "\n"
            pin.get.flush
            
            
            
            val constantsMap: Map[String, String] = (for(constant <- theory.constants) yield {
                val str = pout.get.readLine
                str match {
                    case smt2Model(name, value) => (name -> value)
                    //case _ => Errors.solverError(s"Bad internal smt2 model output: $str")
                }
            }).toMap
            
            val smt2ValueToDomainElement: Map[String, DomainElement] = (
                for((name, value) <- constantsMap if name.charAt(0) == '$')
                    yield (value, Var(name).asDomainElement.get)
            ).toMap
            
            val sortInterpretations: Map[Sort, IndexedSeq[Value]] = (
                for(sort <- theory.sorts) yield sort match{
                    case SortConst(name) => (sort,
                        smt2ValueToDomainElement.values.filter(
                            domainElement => domainElement.sort == sort
                        ).toIndexedSeq)
                    case _ => ???
                }
            ).toMap
            
            val constantInterpretations: Map[AnnotatedVar, Value] =
                (for(constant <- theory.constants) yield {
                    (constant,
                    smtValueToFortressValue(
                        constantsMap(constant.getName),
                        constant.sort,
                        smt2ValueToDomainElement)
                    )
                }).toMap
                
            val functionArgs: Map[FuncDecl, CartesianSeqProduct[Value]] =
                (for(funcDecl <- theory.functionDeclarations) yield {
                    (funcDecl, new CartesianSeqProduct[Value](
                        funcDecl.argSorts
                        .map(sort => sortInterpretations apply sort)
                        .toIndexedSeq))
                }).toMap
            
            for(funcDecl <- theory.functionDeclarations;
                args <- functionArgs.apply(funcDecl)){
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
                
            val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] =
                (for(funcDecl <- theory.functionDeclarations) yield {
                    (funcDecl, (for(args <- functionArgs.apply(funcDecl)) yield {
                        val str = pout.get.readLine
                        val value = str match {
                            case smt2Model(name, value) => value
                            //case _ => Errors.solverError(s"Bad internal smt2 model output: $str")
                        }
                        (args, smtValueToFortressValue(value, funcDecl.resultSort, smt2ValueToDomainElement))
                    }).toMap)
                }).toMap
            
            new BasicInterpretation(sortInterpretations,constantInterpretations,functionInterpretations)
        } catch {
            case ex: IOException => {
                ex.printStackTrace
                new BasicInterpretation(Map(),Map(),Map())
            }
        }
        
    }
    
    private def smtValueToFortressValue(value: String, sort: Sort,
        smt2ValueToDomainElement: Map[String, DomainElement]) : Value = {
        sort match {
            case SortConst(sortName) => smt2ValueToDomainElement.apply(value)
            case _ => ???
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
