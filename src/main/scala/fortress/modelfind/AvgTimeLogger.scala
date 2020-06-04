package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._

import scala.collection.mutable.ListBuffer

// Note: It is the responsibility of the caller to check for timeouts and determine what to do.
// Given a time out, the AvgTimeLogger does nothing.

class AvgTimeLogger extends EventLogger {
    
    private val totalTimes: ListBuffer[Nanoseconds] = ListBuffer.empty
    
    def averageTime: Nanoseconds = {
        Nanoseconds(totalTimes.map(_.value).sum / totalTimes.size)
    }
    
    override def transformerStarted(transformer: ProblemTransformer): Unit = { }
    
    override def transformerFinished(transformer: ProblemTransformer, time: Nanoseconds): Unit = { }
    
    override def allTransformersFinished(finalTheory: Theory, totalTime: Nanoseconds): Unit = { }
    
    override def invokingSolverStrategy(): Unit = { }
    
    def convertingToSolverFormat(): Unit = { }
    
    override def convertedToSolverFormat(time: Nanoseconds): Unit = { }
    
    override def solving(): Unit = { }
    
    override def solverFinished(time: Nanoseconds): Unit = { }
    
    override def finished(result: ModelFinderResult, totalTime: Nanoseconds): Unit = {
        totalTimes += totalTime
    }
    
    override def timeoutInternal(): Unit = { }
}
