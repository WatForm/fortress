package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._
import fortress.logging._
import fortress.msfol

import scala.collection.mutable.ListBuffer

/** Trait which implements standard utilities for the model finder. */
trait ModelFinderSettings extends ModelFinder {
    protected var timeoutMilliseconds: Milliseconds = Milliseconds(60000)
    protected var analysisScopes: Map[Sort,Scope] = Map.empty
    protected var theory: Theory = Theory.empty
    protected var eventLoggers: ListBuffer[EventLogger] = ListBuffer.empty
    
    override def setTheory(newTheory: Theory): Unit = {
        theory = newTheory
    }
    
    override def setTimeout(milliseconds: Milliseconds): Unit = {
        Errors.Internal.precondition(milliseconds >= Milliseconds(0))
        timeoutMilliseconds = milliseconds
    }

    override def setScope(sort: Sort, scope: Scope): Unit = {
        Errors.Internal.precondition(!(sort.name == "Bool"), "Cannot set analysis scope for bool sort.")
        Errors.Internal.precondition(scope.size>0)
        analysisScopes = analysisScopes + (sort -> scope)
    }
    
    override def setExactScope(sort: Sort, size: Int): Unit = {
        Errors.Internal.precondition(size > 0)
        Errors.Internal.precondition(!(sort.name == "Bool"), "Cannot set analysis scope for bool sort.")
        // note that IntSort scopes are specified in bitwidth
        val scope = ExactScope(size)
        analysisScopes = analysisScopes + (sort -> scope)
    }

    override def setNonExactScope(sort: Sort, size: Int): Unit = {
        Errors.Internal.precondition(size > 0)
        Errors.Internal.precondition(!(sort.name == "Bool"), "Cannot set analysis scope for bool sort.")
        // note that IntSort scopes are specified in bitwidth
        val scope = NonExactScope(size)
        analysisScopes = analysisScopes + (sort -> scope)
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
