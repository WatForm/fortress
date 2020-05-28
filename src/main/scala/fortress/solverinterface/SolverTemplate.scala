package fortress.solverinterface

import fortress.msfol._
import fortress.util.StopWatch
import fortress.modelfind._

abstract class SolverTemplate extends SolverStrategy {
    
    @throws(classOf[java.io.IOException])
    override def solve(theory: Theory, timeoutMillis: Int, eventLoggers: Seq[EventLogger]): ModelFinderResult = {
        // template method
        
        for(logger <- eventLoggers) logger.convertingToSolverFormat()
        
        val conversionTimer = new StopWatch
        conversionTimer.startFresh()
        
        convertTheory(theory)
        
        for(logger <- eventLoggers) logger.convertedToSolverFormat(StopWatch.formatNano(conversionTimer.elapsedNano()))
        
        val remainingMillis: Int = timeoutMillis - StopWatch.nanoToMillis(conversionTimer.elapsedNano())
        if(remainingMillis <= 0) {
            for(logger <- eventLoggers) logger.timeoutInternal()
            return ModelFinderResult.Timeout
        }
        
        updateTimeout(remainingMillis)
        
        for(logger <- eventLoggers) logger.solving()
        
        val solverTimer = new StopWatch
        solverTimer.startFresh()
        
        val result: ModelFinderResult = runSolver()
        
        for(logger <- eventLoggers) logger.solverFinished(StopWatch.formatNano(solverTimer.elapsedNano()))
        
        result
    }
    
    protected def convertTheory(theory: Theory): Unit
    protected def updateTimeout(remainingMillis: Int): Unit
    protected def runSolver(): ModelFinderResult
}
