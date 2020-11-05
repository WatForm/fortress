package fortress.compiler

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.logging._
import fortress.util.Control.measureTime
import fortress.util.Control.withCountdown
import fortress.util.Extensions._

trait TransformationCompiler extends LogicCompiler {
    override def compile(
        theory: Theory,
        scopes: Map[Sort, Int],
        timeout: Milliseconds,
        loggers: Seq[EventLogger]
    ): Either[CompilerError, CompilerResult] = {
        val initialProblemState = ProblemState(theory, scopes)

        val finalProblemState = withCountdown(timeout) { countdown => {
            transformerSequence.foldLeft(initialProblemState)((pState, transformer) => {
                if(countdown.isExpired) return Left(CompilerError.Timeout)
                loggers.foreach(_.transformerStarted(transformer))

                val (finalPState, elapsedNano) = measureTime {
                    transformer(pState)
                }

                loggers.foreach(_.transformerFinished(transformer, elapsedNano))

                finalPState
            })
        }}
        
        object Result extends CompilerResult {
            override val theory: Theory = finalProblemState.theory

            override def decompileInterpretation(interpretation: Interpretation): Interpretation = {
                finalProblemState.unapplyInterp.foldLeft(interpretation) {
                    (interp, unapplyFn) => unapplyFn(interp)
                }
            }

            override def skipForNextInterpretation: Set[Declaration] = {
                // We have to use some type hackery to get around the invariance of Set[A]
                (finalProblemState.skolemConstants.map(x => x: Declaration)) union finalProblemState.skolemFunctions.map(x => x: Declaration)
            }
        }
        
        Right(Result)
    }

    def transformerSequence: Seq[ProblemStateTransformer]
}

trait PervasiveTypeChecking extends TransformationCompiler {
    abstract override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformers = super.transformerSequence.toList
        val n = transformers.length
        val typecheckers: List[ProblemStateTransformer] = for(i <- (1 to n).toList) yield new TypecheckSanitizeTransformer
        transformers interleave typecheckers
    }
}