package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._
import fortress.operations.TermOps._
import fortress.compiler.{FortressTHREECompiler, _}
import fortress.msfol.DSL.DSLTerm
import fortress.operations._
import fortress.problemstate._
import fortress.sortinference.SortSubstitution
import fortress.util.Control.measureTime
import fortress.operations.TheoryOps._

import java.util
import java.io._
import scala.jdk.CollectionConverters._
import java.util.concurrent.{Callable, ExecutorService, Executors}
import java.util.concurrent.TimeUnit



class RSVIncrementalModelFinder(solverInterface: SolverInterface, mergeMonotonicSort: Boolean) extends CompilationModelFinder(solverInterface) {

    def this() = this(Z3IncCliInterface, true)

    override def createCompiler(): LogicCompiler = new IncrementalCompiler

    /* the input theory should be pre-compiled */
    def checkMonotonicity(theory: Theory): Map[Sort, Boolean] = {
        new Monotonicity(theory).check()
    }

    def preCompile(theory: Theory): Theory = {
        val timeout = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
        val preCompiler: LogicCompiler = new PreCompiler
        preCompiler.compile(theory, Map.empty, timeout, eventLoggers.toList) match {
            case Left(CompilerError.Timeout) => Errors.Internal.impossibleState("Timeout in pre-compile.")
            case Left(CompilerError.Other(errMsg)) => Errors.Internal.impossibleState(errMsg)
            case Right(compilerRes) => Some(compilerRes).get.theory
        }
    }

    override def checkSat(): ModelFinderResult = {
        totalTimer.startFresh()
        compiler = Some(createCompiler())

        var remainingMillis = timeoutMilliseconds
        var result: ModelFinderResult = UnsatResult

        val newTheory: Theory = {
            val preCompiledTheory: Theory = preCompile(theory)
            if (mergeMonotonicSort) {
                val monotonicityResult = checkMonotonicity(preCompiledTheory)
                val MMS: MergeMonotonicSorts = new MergeMonotonicSorts(preCompiledTheory.sorts.filter(monotonicityResult(_)))
                MMS.updateTheory(preCompiledTheory)
            } else preCompiledTheory
        }
        var scopeMap: Map[Sort, Scope] = newTheory.sorts.map(s => s -> ExactScope(1)).toMap

        do {
            result = {
                remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
                compiler.get.compile(newTheory, scopeMap, remainingMillis, eventLoggers.toList) match {
                    case Left(CompilerError.Timeout) => TimeoutResult
                    case Left(CompilerError.Other(errMsg)) => ErrorResult(errMsg)
                    case Right(compilerRes) => {
                        compilerResult = Some(compilerRes)
                        val finalTheory = compilerResult.get.theory
                        notifyLoggers(_.allTransformersFinished(finalTheory, totalTimer.elapsedNano()))
                        solverPhase(finalTheory)
                    }
                }
            }
            if (result == UnsatResult) {
                val unsatCore: String = solverSession.get.unsatCore
                val constraints: Seq[String] = unsatCore.substring(1, unsatCore.length - 1).split(" ")
                if (constraints.nonEmpty && constraints.head != "") {
                    for (con <- constraints) {
                        val sort: Sort = SortConst(con.split("_").head)
                        scopeMap += (sort -> ExactScope(scopeMap(sort).size + 1))
                    }
                }
                println("trying scope: " + scopeMap)
//                scopeMap.foreach(item => print(item._2.size + ", " ))
//                print("\n")
            }
        } while (result == UnsatResult)

        result
    }

}

