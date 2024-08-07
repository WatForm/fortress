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



// these are definitions that are common for all compilers

abstract class BaseCompiler extends Compiler {

    override def compile(
        theory: Theory,
        scopes: Map[Sort, Scope],
        timeout: Milliseconds,
        loggers: Seq[EventLogger],
        verbose: Boolean,
    ): Either[CompilerError, CompilerResult] = {

        //println("in base compiler compile")
        val initialProblemState = ProblemState(theory, scopes, verbose)

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