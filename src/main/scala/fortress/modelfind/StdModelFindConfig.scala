package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._

import scala.collection.mutable.ListBuffer

trait StdModelFindConfig extends ModelFinder {
    protected var timeoutMilliseconds: Milliseconds = Milliseconds(60000)
    protected var analysisScopes: Map[Sort, Int] = Map.empty
    protected var theory: Theory = Theory.empty
    protected var integerSemantics: IntegerSemantics = Unbounded
    protected var debug: Boolean = false
    protected var eventLoggers: ListBuffer[EventLogger] = ListBuffer.empty
    
    override def setTheory(newTheory: Theory): Unit = {
        theory = newTheory
    }
    
    override def setTimeout(milliseconds: Int): Unit = {
        Errors.precondition(milliseconds >= 0)
        timeoutMilliseconds = Milliseconds(milliseconds)
    }
    
    override def setAnalysisScope(t: Sort, size: Int): Unit = {
        Errors.precondition(size >= 0)
        analysisScopes = analysisScopes + (t -> size)
    }
    
    override def setBoundedIntegers(semantics: IntegerSemantics): Unit = {
        integerSemantics = semantics
    }
    
    override def setOutput(writer: java.io.Writer): Unit = {
        eventLoggers += new StandardLogger(writer)
    }
    
    override def addLogger(logger: EventLogger): Unit = {
        eventLoggers += logger
    }
    
    // Calculate the number of nanoseconds until we must output TIMEOUT
    protected def timeoutNano: Nanoseconds = timeoutMilliseconds.toNano
}
