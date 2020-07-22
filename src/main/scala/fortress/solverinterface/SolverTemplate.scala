package fortress.solverinterface

import fortress.msfol._
import fortress.util._
import fortress.modelfind._

abstract class SolverTemplate extends SolverStrategy {
    
    override def solve(theory: Theory, timeoutMillis: Milliseconds, eventLoggers: Seq[EventLogger]): ModelFinderResult = {
        // template method
        
        for(logger <- eventLoggers) logger.convertingToSolverFormat()
        
        val conversionTimer = new StopWatch
        conversionTimer.startFresh()
        
        convertTheory(theory)
        
        for(logger <- eventLoggers) logger.convertedToSolverFormat(conversionTimer.elapsedNano())
        
        val remainingMillis = timeoutMillis - conversionTimer.elapsedNano().toMilli
        if(remainingMillis <= Milliseconds(0)) {
            for(logger <- eventLoggers) logger.timeoutInternal()
            return ModelFinderResult.Timeout
        }
        
        updateTimeout(remainingMillis)
        
        for(logger <- eventLoggers) logger.solving()
        
        val solverTimer = new StopWatch
        solverTimer.startFresh()
        
        val result: ModelFinderResult = runSolver()
        
        for(logger <- eventLoggers) logger.solverFinished(solverTimer.elapsedNano())
        logSMT2Output(eventLoggers)
        
        result
    }
    
    def logSMT2Output(eventLoggers: Seq[EventLogger]): Unit = { }
    
    protected def convertTheory(theory: Theory): Unit
    protected def updateTimeout(remainingMillis: Milliseconds): Unit
    protected def runSolver(): ModelFinderResult
}
