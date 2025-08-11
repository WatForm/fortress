/*
 * The purpose of this compiler is to 
 * run two different integer schemes on the same 
 * theory and then merge the results (without duplications)
 * to create a problem that is satisfiable for instances
 * that satisfy the first integer scheme but not 
 * the second.
 */

package fortress.compilers

import scala.collection.mutable.ListBuffer
import fortress.msfol._
import fortress.util._
import fortress.interpretation._
import fortress.logging._
import fortress.operations.TermOps._
import fortress.problemstate._
import fortress.transformers._
import fortress.util.Control.measureTime
import fortress.util.Control.withCountdown
import fortress.operations.TheoryOps

class SemCompIntCompiler extends Compiler {

    // we have to change the entire definition of compile from what
    // was in BaseCompiler
    override def compile(
        theory: Theory,
        scopes: Map[Sort, Scope],
        timeout: Milliseconds,
        loggers: Seq[EventLogger],
        verbose: Boolean,
        forceFullCompile: Boolean,
    ): Either[CompilerError, StandardCompilerResult] = {
 
        // println("in SemCompIntCompiler compile")
        val initialProblemState = ProblemState(theory, scopes, verbose)

        // two compilers to compare are hardcoded here
        val ts1 = new IntCompiler(IntNOBVTransformer).transformerSequence
        val ts2 = new IntCompiler(IntOPFITransformer).transformerSequence

        // take a problem state and apply a seq of transformers to it
        // returns with (and folds over) an Either[CompilerError, StandardCompilerResult]
        def doFold(initPState:ProblemState, transSeq:Seq[ProblemStateTransformer])
                :Either[CompilerError, StandardCompilerResult] = {
            val initResult = Right(new StandardCompilerResult(initPState))
            val finalResult = withCountdown(timeout) { countdown => {
                // fold is over [Either[CompilerError, StandardCompilerResult], transformer] type
                transSeq.foldLeft(initResult)((result:Either[CompilerError, StandardCompilerResult], transformer) => {
                 result match {
                   case Left(_) => 
                        // CompilerError  
                        // probably will have exited function earlier
                        return result  
                   case Right(stdCompResult) => {
                        if(countdown.isExpired) 
                            // return from doFold function
                            return Left(CompilerError.Timeout)
                    
                        loggers.foreach(_.transformerStarted(transformer))

                        val (finalPState, elapsedNano) = measureTime {
                            transformer(stdCompResult.finalProblemState)
                        }
                        if (verbose) {
                            // not perfect b/c it only prints the theory
                            println("After "+transformer.getClass.getName)
                            println(TheoryOps.wrapTheory(finalPState.theory).smtlib)
                        }
                        loggers.foreach(_.transformerFinished(transformer, elapsedNano))

                        // trivial result is not a reason to quit early in a comparison
                        //if (!forceFullCompile && finalPState.flags.trivialResult.isDefined)
                        //            return Right(new Result(finalPState))

                        Right(new StandardCompilerResult(finalPState))
                    }
 
 
                 }})}}
            // already wrapped in a Left or Right
            finalResult
        }            

        val ts1finalProblemState = 
            doFold(initialProblemState, ts1) match {
                // return from compile
                case Left(x) => return Left(x)
                case Right(stdCompilerResult) => stdCompilerResult.finalProblemState
            }

        val ts2finalProblemState = 
           doFold(initialProblemState, ts2) match {
                // return from compile
                case Left(x) => return Left(x)
                case Right(stdCompilerResult) => stdCompilerResult.finalProblemState
            }

        val tsmerge:Seq[ProblemStateTransformer] = { 
            val ts = CompilersRegistry.NullTransformerList
            ts += new MergeFiniteIntTheoriesTransformer(ts1finalProblemState)
            // for safety, typecheck it again
            ts += TypecheckSanitizeTransformer
            ts.toList
        }

        val mergedFinalProblemState = 
           doFold(ts2finalProblemState, tsmerge) match {
                // return from compile
                case Left(x) => return Left(x)
                case Right(stdCompilerResult) => stdCompilerResult.finalProblemState
            }
        if (verbose) {
            // not perfect b/c it only prints the theory
            println(TheoryOps.wrapTheory(mergedFinalProblemState.theory).smtlib)
        }
        Right(new StandardCompilerResult(mergedFinalProblemState))
    }

    // not used but must have a value
    override def transformerSequence: Seq[ProblemStateTransformer] = {
       Errors.Internal.impossibleState("transformerSequence of SemCompareIntCompiler called")
    }

}
