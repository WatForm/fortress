package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._

class StandardLogger(writer: java.io.Writer) extends EventLogger {
    
    override def transformerStarted(transformer: ProblemTransformer): Unit = {
        writer.write("Applying transformer: " + transformer.name)
        writer.write("... ")
        writer.flush()
    }
    
    override def transformerFinished(transformer: ProblemTransformer, time: String): Unit = {
        writer.write(time + "\n")
        writer.flush
    }
    
    override def allTransformersFinished(finalTheory: Theory, totalTime: String): Unit = {
        writer.write("Total transformation time: " + totalTime + "\n")
        writer.flush()
    }
    
    override def invokingSolverStrategy(): Unit = {
        writer.write("Invoking solver strategy...\n")
        writer.flush()
    }
    
    def convertingToSolverFormat(): Unit = {
        writer.write("Converting to solver format: ")
        writer.flush()
    }
    
    override def convertedToSolverFormat(time: String): Unit = {
        writer.write(time + "\n")
        writer.flush()
    }
    
    override def solving(): Unit = {
        writer.write("Solving... ")
        writer.flush()
    }
    
    override def solverFinished(time: String): Unit = {
        writer.write("Z3 solver time: " + time + "\n")
        writer.flush()
    }
    
    override def finished(result: ModelFinderResult, totalTime: String): Unit = {
        writer.write("Done. Result was " + result.toString + ".\n")
        writer.write("TOTAL time: " + totalTime + "\n")
        writer.flush()
    }
    
    override def timeoutInternal(): Unit = {
        writer.write("TIMEOUT within Fortress.\n")
        writer.flush()
    }
    
}
