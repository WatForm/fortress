package fortress.solverinterface

import java.io._

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._
import fortress.solverinterface._
import fortress.operations.SmtlibConverter

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
    
    override def runSolver(): ModelFinderResult = {
        tryIO(() => {
            clearCVC4
            startCVC4()
            convertedBytes writeTo pin.get
            checkSat
        })
    }
    
    def checkSat(): ModelFinderResult = {
        pin.get write "(check-sat)\n"
        
        pin.get.flush
        
        var result = pout.get.readLine
        result match {
            case "sat" => ModelFinderResult.Sat
            case "unsat" => ModelFinderResult.Unsat
            case _ => ModelFinderResult.Unknown
        }
    }
    
    def addAxiom(axiom: Term, timeoutMillis: Milliseconds): ModelFinderResult = {
        Errors.verify(process.nonEmpty, "Cannot add axiom without a live cvc4 session")
        tryIO(() => {
            val converter = new SmtlibConverter(pin.get)
            converter writeAssertion axiom
            
            checkSat
        })
    }

    def getInstance(theory: Theory): Interpretation = {
        ???
    }
    
    def tryIO(func: () => ModelFinderResult): ModelFinderResult = {
        try {
            func()
        } catch {
            case ex: IOException => {
                clearCVC4
                ModelFinderResult.Error
            }
        }
    }
    
    def startCVC4(): Unit = {
        process = Some(new ProcessBuilder(processArgs).start())
        pin = Some(new BufferedWriter(new OutputStreamWriter(process.get.getOutputStream)))
        pout = Some(new BufferedReader(new InputStreamReader(process.get.getInputStream)))
    }
    
    def clearCVC4: Unit = {
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
    
    def processArgs: java.util.List[String]
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
