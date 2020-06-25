package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._

import scala.collection.mutable

// Note: It is the responsibility of the caller to check for timeouts and determine what to do.
// Given a time out, the AvgTimeLogger does nothing.

class AvgTimeDetailedLogger extends EventLogger {
    
    private val totalTimes: mutable.ListBuffer[Nanoseconds] = mutable.ListBuffer.empty
    
    private val transformerTimes: mutable.Map[String, mutable.ListBuffer[Nanoseconds]] = mutable.Map()
    
    private var solverConvertTimes: mutable.ListBuffer[Nanoseconds] = mutable.ListBuffer.empty
    
    private var solverRunTimes: mutable.ListBuffer[Nanoseconds] = mutable.ListBuffer.empty
    
    def averageTime: Nanoseconds = {
        Nanoseconds(totalTimes.map(_.value).sum / totalTimes.size)
    }
    
    def averageTransformerTimes: Map[String, Nanoseconds] = transformerTimes.map{
        case(name, times) => name -> Nanoseconds(times.map(_.value).sum / times.size)
    }.toMap
    
    def averageConversionTime: Nanoseconds = {
        Nanoseconds(solverConvertTimes.map(_.value).sum / solverConvertTimes.size)
    }
    
    def averageSolverTime: Nanoseconds = {
        Nanoseconds(solverRunTimes.map(_.value).sum / solverRunTimes.size)
    }
    
    ////////////
    
    override def transformerStarted(transformer: ProblemStateTransformer): Unit = { }
    
    override def transformerFinished(transformer: ProblemStateTransformer, time: Nanoseconds): Unit = {
        if(!(transformerTimes contains transformer.name)) {
            transformerTimes(transformer.name) = mutable.ListBuffer.empty
        }
        transformerTimes(transformer.name) += time
    }
    
    override def allTransformersFinished(finalTheory: Theory, totalTime: Nanoseconds): Unit = { }
    
    override def invokingSolverStrategy(): Unit = { }
    
    def convertingToSolverFormat(): Unit = { }
    
    override def convertedToSolverFormat(time: Nanoseconds): Unit = {
        solverConvertTimes += time 
    }
    
    override def solving(): Unit = { }
    
    override def solverFinished(time: Nanoseconds): Unit = {
        solverRunTimes += time
    }
    
    override def finished(result: ModelFinderResult, totalTime: Nanoseconds): Unit = {
        totalTimes += totalTime
    }
    
    override def timeoutInternal(): Unit = { }
}
