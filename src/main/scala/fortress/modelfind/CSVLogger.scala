package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._

class CSVLogger(writer: java.io.Writer) extends EventLogger {
    
    override def transformerStarted(transformer: ProblemTransformer): Unit = { }
    
    override def transformerFinished(transformer: ProblemTransformer, time: Nanoseconds): Unit = {
        writer.write(transformer.name.toLowerCase + "," + time.prettyPrint + "\n")
        writer.flush()
    }
    
    override def allTransformersFinished(finalTheory: Theory, totalTime: Nanoseconds): Unit = {
        writer.write("transformation total," + totalTime.prettyPrint + "\n")
        writer.flush()
    }
    
    override def invokingSolverStrategy(): Unit = { }
    
    def convertingToSolverFormat(): Unit = { }
    
    override def convertedToSolverFormat(time: Nanoseconds): Unit = {
        writer.write("solver format conversion," + time.prettyPrint + "\n")
        writer.flush()
    }
    
    override def solving(): Unit = { }
    
    override def solverFinished(time: Nanoseconds): Unit = {
        writer.write("z3 solver," + time.prettyPrint + "\n")
        writer.flush()
    }
    
    override def finished(result: ModelFinderResult, totalTime: Nanoseconds): Unit = {
        writer.write("result," + result.toString + "\n")
        writer.write("total," + totalTime.prettyPrint + "\n")
        writer.flush()
    }
    
    override def timeoutInternal(): Unit = {
        writer.write("total,timeout")
        writer.flush()
    }
}
