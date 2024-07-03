package fortress.compilers

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.logging._
import fortress.operations.TermOps._
import fortress.problemstate._
import fortress.util.Control.measureTime
import fortress.util.Control.withCountdown
import fortress.util.Extensions._

/**
  * Converts a theory with scopes into another ``lower-level" theory, intended to be sent to an external solver.
  * Performs this process through a sequence of transformations.
  */
abstract class Compiler {

    def transformerSequence: Seq[ProblemStateTransformer]
        
    def compile(
        theory: Theory,
        scopes: Map[Sort, Scope],
        timeout: Milliseconds,
        loggers: Seq[EventLogger],
        verbose: Boolean,
    ): Either[CompilerError, CompilerResult] = {
        val initialProblemState = ProblemState(theory, scopes, verbose)

        val finalProblemState = withCountdown(timeout) { countdown => {
            transformerSequence.foldLeft(initialProblemState)((pState, transformer) => {
                if(countdown.isExpired) return Left(CompilerError.Timeout)
                loggers.foreach(_.transformerStarted(transformer))

//                println(s"Theory before ${transformer.name}:\n-----")
//                println(Dump.theoryToSmtlibTC(pState.theory))
//                println("-----")
                val (finalPState, elapsedNano) = measureTime {
                    transformer(pState)
                }

                loggers.foreach(_.transformerFinished(transformer, elapsedNano))

                finalPState
            })
        }}

//        println(s"Final theory:\n-----")
//        println(Dump.theoryToSmtlibTC(finalProblemState.theory))
//        println("-----")

        object Result extends CompilerResult {
            override val theory: Theory = finalProblemState.theory

            override def decompileInterpretation(interpretation: Interpretation): Interpretation = {
                finalProblemState.unapplyInterp.foldLeft(interpretation) {
                    (interp, unapplyFn) => unapplyFn(interp)
                }
            }

            override val skipForNextInterpretation: Set[Declaration] = {
                // We have to use some type hackery to get around the invariance of Set[A]
                (finalProblemState.skolemConstants.map(x => x: Declaration)) union finalProblemState.skolemFunctions.map(x => x: Declaration)
            }

            override def eliminateDomainElements(term: Term): Term = {
                if (finalProblemState.flags.distinctConstants) {
                    term.eliminateDomainElementsConstants
                } else {
                    term.eliminateDomainElementsEnums
                }
            }
        }
        Right(Result)
    }

}

/**
  * For debugging purposes, interleaves type-checking after each step of the parent compiler's transformers.
  * This should not be done in production code, since it will slow things down.
  */
trait PervasiveTypeChecking extends Compiler {
    abstract override def transformerSequence: Seq[ProblemStateTransformer] = {
        val transformers = super.transformerSequence.toList
        val n = transformers.length
        val typecheckers: List[ProblemStateTransformer] = for(i <- (1 to n).toList) yield TypecheckSanitizeTransformer
        transformers interleave typecheckers
    }
}