package fortress.solverinterface

import java.io._

import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._
import fortress.solverinterface._
import fortress.operations.SmtlibConverter

abstract class ProcessBuilderSolver extends SolverStrategy {
    private var process: Process = null
    private var pin: BufferedWriter = null
    private var pout: BufferedReader = null
    /**
    * Attempts to solve the given theory, searching for a satisfying instance.
    */
    @throws(classOf[java.io.IOException])
    def solve(theory: Theory, timeoutMillis: Milliseconds, eventLoggers: Seq[EventLogger]): ModelFinderResult = {
        tryIO (() => {
            clearCVC4
            startCVC4(timeoutMillis)
            pin write "(set-option :produce-models true)\n"
            pin write "(set-logic ALL)\n"
            val converter = new SmtlibConverter(pin)
            converter writeTheory theory
            //logging
            //var errLogger = new BufferedWriter(new OutputStreamWriter(System.err))
            //val converter2 = new SmtlibConverter(errLogger)
            //converter2 writeTheory theory
            //errLogger.flush
            checkSat
        })
    }
    
    def addAxiom(axiom: Term, timeoutMillis: Milliseconds): ModelFinderResult = {
        Errors.verify(process != null, "Cannot add axiom without a live cvc4 session")
        tryIO(() => {
            val converter = new SmtlibConverter(pin)
            converter writeAssertion axiom
            
            checkSat
        })
    }

    def getInstance(theory: Theory): Interpretation = {
        null
    }
    
    def checkSat: ModelFinderResult = {
        tryIO(() => {
            pin write "(check-sat)\n"
            
            pin.flush
            
            var result = pout.readLine
            result match {
                case "sat" => ModelFinderResult.Sat
                case "unsat" => ModelFinderResult.Unsat
                case _ => ModelFinderResult.Unknown
            }
        })
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
    
    def startCVC4(timeoutMillis: Milliseconds): Unit = {
        process = new ProcessBuilder(processArgs(timeoutMillis)).start()
        pin = new BufferedWriter(new OutputStreamWriter(process.getOutputStream))
        pout = new BufferedReader(new InputStreamReader(process.getInputStream))
    }
    
    def clearCVC4: Unit = {
        finalize
        pin = null
        pout = null
        process = null
    }
    
    override protected def finalize: Unit = {
        if(process != null) {
            pin.close
            pout.close
            process.destroy
        }
    }
    
    def processArgs(timeoutMillis: Milliseconds): java.util.List[String]
}

class CVC4CliSolver extends ProcessBuilderSolver {
    def processArgs(timeoutMillis: Milliseconds): java.util.List[String] = {
        java.util.List.of("cvc4", "--lang=smt2.6", "-im", "--tlimit-per=" + timeoutMillis.value)
    }
}

class Z3CliSolver extends ProcessBuilderSolver {
    def processArgs(timeoutMillis: Milliseconds): java.util.List[String] = {
        java.util.List.of("z3", "-smt2", "-in", "-t:" + timeoutMillis.value)
    }
}
