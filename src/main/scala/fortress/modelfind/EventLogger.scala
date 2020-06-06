package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._

trait EventLogger {
    def transformerStarted(transformer: ProblemTransformer): Unit
    def transformerFinished(transformer: ProblemTransformer, time: Nanoseconds): Unit
    def allTransformersFinished(finalTheory: Theory, totalTime: Nanoseconds): Unit
    def invokingSolverStrategy(): Unit
    def convertingToSolverFormat(): Unit
    def convertedToSolverFormat(time: Nanoseconds): Unit
    def solving(): Unit
    def solverFinished(time: Nanoseconds): Unit
    def finished(result: ModelFinderResult, time: Nanoseconds): Unit
    def timeoutInternal(): Unit
}
