package fortress.modelfind

import fortress.msfol._
import fortress.transformers._

trait EventLogger {
    def transformerStarted(transformer: ProblemTransformer): Unit
    def transformerFinished(transformer: ProblemTransformer, time: String): Unit
    def allTransformersFinished(finalTheory: Theory, totalTime: String): Unit
    def invokingSolverStrategy(): Unit
    def convertingToSolverFormat(): Unit
    def convertedToSolverFormat(time: String): Unit
    def solving(): Unit
    def solverFinished(time: String): Unit
    def finished(result: ModelFinderResult, time: String): Unit
    def timeoutInternal(): Unit
}
