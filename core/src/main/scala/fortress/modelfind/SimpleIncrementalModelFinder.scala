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
import fortress.util.Control.measureTime
import scala.collection.mutable
import fortress.problemstate._

abstract class SimpleIncrementalModelFinder(solverInterface: SolverInterface)
extends CompilationModelFinder(solverInterface) {

    override def checkSat(): ModelFinderResult = {
        /*
            Cannot use incremental soling if all the sorts are assigned with scopes.
            Just throw out an error.
         */
        Errors.Internal.precondition(
            analysisScopes.size < theory.sorts.size,
            " All the sorts are bounded with scopes, cannot use incremental solving.\n " +
                "Please try normal model finders."
        )

        totalTimer.startFresh()
        compiler = Some(createCompiler())

        val unboundedSorts: IndexedSeq[Sort] = theory.sorts.filterNot(s => {
            analysisScopes.contains(s)
        }).toIndexedSeq
        val unboundedSortNum = unboundedSorts.size

        val minScope: IndexedSeq[Int] = for(i <- 1 to unboundedSortNum) yield 1
        val space = new mutable.Queue[IndexedSeq[Int]]
        space += minScope

        var result: ModelFinderResult = UnsatResult
        var times: Int = 0

        def getScopeMap: Map[Sort, Scope] = {
            var map: Map[Sort, Scope] = Map.empty
            val scope = space.dequeue()
            for(i <- 0 until unboundedSortNum) {
                val tmp = for(j <- 0 until unboundedSortNum) yield if(i==j) scope(j)+1 else scope(j)
                if(!space.contains(tmp)) space.enqueue(tmp)
            }
            for(i <- 0 until unboundedSortNum) map = map + (unboundedSorts(i) -> ExactScope(scope(i)))
            map ++ analysisScopes
        }

        do {
            times += 1
            val scopeMap = getScopeMap
            result = {
                compiler.get.compile(theory, scopeMap, timeoutMilliseconds, eventLoggers.toList) match {
                    case Left(CompilerError.Timeout) => TimeoutResult
                    case Left(CompilerError.Other(errMsg)) => ErrorResult(errMsg)
                    case Right(compilerRes) => {
                        compilerResult = Some(compilerRes)
                        val finalTheory = compilerResult.get.theory
                        notifyLoggers(_.allTransformersFinished(finalTheory, totalTimer.elapsedNano))
                        val finalResult: ModelFinderResult = solverPhase(finalTheory)
                        finalResult
                    }
                }
            }
        } while (result ==  UnsatResult)

        result
    }

}
