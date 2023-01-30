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
import fortress.problemstate._
import fortress.util.Control.measureTime

import scala.collection.mutable

abstract class RSVIncrementalModelFinder(solverInterface: SolverInterface)
extends CompilationModelFinder(solverInterface) {

    def getUnsatCore: String = solverSession.get.unsatCore

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

        var result: ModelFinderResult = UnsatResult
        var times: Int = 0

        val unboundedSorts: IndexedSeq[Sort] = theory.sorts.filterNot(s => {
            analysisScopes.contains(s)
        }).toIndexedSeq
        val unboundedSortNum = unboundedSorts.size
//
//        val minScope: IndexedSeq[Int] = for (i <- 1 to unboundedSortNum) yield 1
//        val space = new mutable.Queue[IndexedSeq[Int]]
//        space += minScope

//        def isValidScope(scopes: IndexedSeq[Int]): Boolean = ???

//        def getScope: Map[Sort, Scope] = {
//            Errors.Internal.precondition(space.nonEmpty, "Searching space is empty, the problem is unsatisfiable.")
//            var map: Map[Sort, Scope] = Map.empty
//            val scope = space.dequeue()
//            for (i <- 0 until unboundedSortNum) {
//                val tmp = for (j <- 0 until unboundedSortNum) yield if (i == j) scope(j) + 1 else scope(j)
//                if (!space.contains(tmp) && isValidScope(tmp)) space.enqueue(tmp)
//            }
//            if (isValidScope(scope)) {
//                for (i <- 0 until unboundedSortNum) map = map + (unboundedSorts(i) -> ExactScope(scope(i)))
//                map + analysisScopes
//            } else {
//                getScope
//            }
//        }

        var scopeMap: Map[Sort, Scope] = {
            var map = Map.empty
            for(sort <- unboundedSorts) map = map + (sort -> ExactScope(1))
            map + analysisScopes
        }

        do {
            times += 1
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

            if(result == UnsatResult) {
                val unsatCore: String = getUnsatCore
                val constraints: Seq[String] = unsatCore.substring(1, unsatCore.length-1).split(" ")
                if(constraints.nonEmpty && constraints.head != "") {
                    for(con <- constraints) {
                        val sort: Sort = SortConst(con.split("_").head)
                        scopeMap += ( sort -> ExactScope(scopeMap(sort).size + 1) )
                    }
                }
            }

        } while (result == UnsatResult)

        println("Got result in " + times + " times checking.")
        result
    }

}

