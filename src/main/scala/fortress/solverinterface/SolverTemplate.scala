package fortress.solverinterface

import fortress.msfol._
import fortress.util.StopWatch
import fortress.modelfind._

abstract class SolverTemplate extends SolverStrategy {
    
    @throws(classOf[java.io.IOException])
    override def solve(theory: Theory, timeoutMillis: Int, log: java.io.Writer): ModelFinderResult = {
        // template method
        
        log.write("Converting to solver format: ")
        log.flush()
        
        val conversionTimer = new StopWatch
        conversionTimer.startFresh()
        
        convertTheory(theory, log)
        
        log.write(StopWatch.formatNano(conversionTimer.elapsedNano()) + "\n")
        log.flush()
        
        val remainingMillis: Int = timeoutMillis - StopWatch.nanoToMillis(conversionTimer.elapsedNano())
        if(remainingMillis <= 0) {
            log.write("TIMEOUT within Fortress.\n")
            log.flush()
            return ModelFinderResult.Timeout
        }
        
        updateTimeout(remainingMillis)
        
        log.write("Solving... ")
        log.flush()
        
        val solverTimer = new StopWatch
        solverTimer.startFresh()
        
        val result: ModelFinderResult = runSolver(log)
        
        log.write("Z3 solver time: " + StopWatch.formatNano(solverTimer.elapsedNano()) + "\n")
        
        result
    }
    
    protected def convertTheory(theory: Theory, log: java.io.Writer): Unit
    protected def updateTimeout(remainingMillis: Int): Unit
    protected def runSolver(log: java.io.Writer): ModelFinderResult
}
