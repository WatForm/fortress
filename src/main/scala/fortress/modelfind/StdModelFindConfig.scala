package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._

trait StdModelFindConfig extends ModelFinder {
    protected var timeoutMilliseconds: Int = 60000
    protected var analysisScopes: Map[Sort, Int] = Map.empty
    protected var theory: Theory = Theory.empty
    protected var integerSemantics: IntegerSemantics = Unbounded
    protected var log: java.io.Writer = new java.io.PrintWriter(new fortress.data.NullOutputStream)
    protected var debug: Boolean = false
    
    override def setTheory(newTheory: Theory): Unit = {
        theory = newTheory
    }
    
    override def setTimeout(milliseconds: Int): Unit = {
        Errors.precondition(milliseconds >= 0)
        timeoutMilliseconds = milliseconds
    }
    
    override def setAnalysisScope(t: Sort, size: Int): Unit = {
        Errors.precondition(size >= 0)
        analysisScopes = analysisScopes + (t -> size)
    }
    
    override def setBoundedIntegers(semantics: IntegerSemantics): Unit = {
        integerSemantics = semantics
    }
    
    override def setDebug(enableDebug: Boolean): Unit = {
        debug = enableDebug
    }
    
    override def setOutput(logWriter: java.io.Writer) = {
        log = logWriter
    }
    
    // Calculate the number of nanoseconds until we must output TIMEOUT
    protected def timeoutNano: Long = StopWatch.millisToNano(timeoutMilliseconds)
}
