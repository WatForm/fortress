package fortress.compilers

import fortress.msfol._
import fortress.util._
import fortress.interpretation._
import fortress.logging._
import fortress.operations.TermOps._
import fortress.problemstate._
import fortress.util.Control.measureTime
import fortress.util.Control.withCountdown
import fortress.operations.TheoryOps

// these are definitions that are common for all compilers

abstract class BaseCompiler extends Compiler {

    override def compile(
        theory: Theory,
        scopes: Map[Sort, Scope],
        timeout: Milliseconds,
        loggers: Seq[EventLogger],
        verbose: Boolean,
        forceFullCompile: Boolean,
    ): Either[CompilerError, StandardCompilerResult] = {

        //println("in base compiler compile")
        val initialProblemState = ProblemState(theory, scopes, verbose)

        val finalProblemState = withCountdown(timeout) { countdown => {
            transformerSequence.foldLeft(initialProblemState)((pState, transformer) => {
                if(countdown.isExpired) return Left(CompilerError.Timeout)
                loggers.foreach(_.transformerStarted(transformer))

                val (finalPState, elapsedNano) = measureTime {
                    transformer(pState)
                }
                if (verbose) {
                    // not perfect b/c it only prints the theory
                    println(TheoryOps.wrapTheory(finalPState.theory).smtlib)
                }
                loggers.foreach(_.transformerFinished(transformer, elapsedNano))

                if (!forceFullCompile && finalPState.flags.trivialResult.isDefined)
                    return Right(new StandardCompilerResult(finalPState))

                finalPState
            })
        }}

//        println(s"Final theory:\n-----")
//        println(Dump.theoryToSmtlibTC(finalProblemState.theory))
//        println("-----")

        Right(new StandardCompilerResult(finalProblemState))
    }

}