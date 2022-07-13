package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._
import fortress.logging._

import scala.collection.mutable.ListBuffer

/** Trait which implements standard utilities for the model finder. */
trait ModelFinderSettings extends ModelFinder {
    protected var timeoutMilliseconds: Milliseconds = Milliseconds(60000)
    protected var analysisScopes: Map[Sort, Int] = Map.empty
    protected var theory: Theory = Theory.empty
    protected var eventLoggers: ListBuffer[EventLogger] = ListBuffer.empty
    
    override def setTheory(newTheory: Theory): Unit = {
        theory = newTheory
    }
    
    override def setTimeout(milliseconds: Milliseconds): Unit = {
        Errors.Internal.precondition(milliseconds >= Milliseconds(0))
        timeoutMilliseconds = milliseconds
    }
    
    override def setAnalysisScope(t: Sort, size: Int): Unit = {
        Errors.Internal.precondition(size >= 0)
        // note that IntSort scopes are specified in bitwidth
        analysisScopes = analysisScopes + (t -> size)
    }
    
    override def setOutput(writer: java.io.Writer): Unit = {
        eventLoggers += new StandardLogger(writer)
    }
    
    override def addLogger(logger: EventLogger): Unit = {
        eventLoggers += logger
    }
    
    // Calculate the number of nanoseconds until we must output TIMEOUT
    protected def timeoutNano: Nanoseconds = timeoutMilliseconds.toNano
    
    protected def notifyLoggers(notifyFn: EventLogger => Unit): Unit = for(logger <- eventLoggers) notifyFn(logger)
}
