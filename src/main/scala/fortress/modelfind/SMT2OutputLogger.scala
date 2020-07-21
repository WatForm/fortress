package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._

class SMT2OutputLogger(writer: java.io.Writer) extends EventLogger {
    override def transformerStarted(transformer: ProblemStateTransformer): Unit = { }
    override def transformerFinished(transformer: ProblemStateTransformer, time: Nanoseconds): Unit = { }
    override def allTransformersFinished(finalTheory: Theory, totalTime: Nanoseconds): Unit = { }
    override def invokingSolverStrategy(): Unit = { }
    override def convertingToSolverFormat(): Unit = { }
    override def convertedToSolverFormat(time: Nanoseconds): Unit = { }
    override def solving(): Unit = { }
    override def solverFinished(time: Nanoseconds): Unit = { }
    override def finished(result: ModelFinderResult, time: Nanoseconds): Unit = { }
    override def timeoutInternal(): Unit = { }
    
    override def smt2Output(smt2String: String): Unit = {
        writer.write(smt2String);
    }
}
