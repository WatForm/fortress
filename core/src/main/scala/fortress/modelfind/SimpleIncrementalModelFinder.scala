package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._
import fortress.operations.TermOps._
import fortress.compiler._
import fortress.logging._
import fortress.msfol.DSL.DSLTerm
import fortress.operations._
import fortress.util.Control.measureTime

import scala.collection.mutable
import fortress.problemstate._
class SimpleIncrementalModelFinder(solverInterface: SolverInterface, useMonotonicity: Boolean)
extends CompilationModelFinder(solverInterface) {

    def this() = this(Z3IncCliInterface, false)

    override def createCompiler(): LogicCompiler = new FortressTHREECompiler

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
            if (useMonotonicity) {
                val monotonicityResult = checkMonotonicity(preCompiledTheory)
                val MMS: MergeMonotonicSorts = new MergeMonotonicSorts(preCompiledTheory.sorts.filter(monotonicityResult(_)))
                MMS.updateTheory(preCompiledTheory)
            } else preCompiledTheory
        }
        val sortNum: Int = newTheory.sorts.size
        val sorts: IndexedSeq[Sort] = newTheory.sorts.toIndexedSeq

        val minScope: IndexedSeq[Int] = for(i <- 1 to sortNum) yield 1
        val space = new mutable.Queue[IndexedSeq[Int]]
        space += minScope


        def getScopeMap: Map[Sort, Scope] = {
            var map: Map[Sort, Scope] = Map.empty
            val scope = space.dequeue()
            for(i <- 0 until sortNum) {
                val tmp = for(j <- 0 until sortNum) yield if(i==j) scope(j)+1 else scope(j)
                if(!space.contains(tmp)) space.enqueue(tmp)
            }
            for(i <- 0 until sortNum) map = map + (sorts(i) -> ExactScope(scope(i)))
            map
        }

        do {
            val scopeMap = getScopeMap
            remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
            result = {
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
        } while (result ==  UnsatResult)

        result
    }

}
