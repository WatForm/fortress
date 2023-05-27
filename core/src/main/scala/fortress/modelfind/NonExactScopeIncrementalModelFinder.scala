package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._
import fortress.operations.TermOps._
import fortress.compiler._
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

/*
    Try to find a group of scopes to satisfy the theory by setting non-exact scope.
    For monotonic sorts, if no model exists for domain size n then no model can exist where n is smaller, therefore, we only need to set non-exact scope for non-monotonic sorts.
 */

class NonExactScopeIncrementalModelFinder(solverInterface: SolverInterface, useMonotonicity: Boolean, startSize: Int) extends CompilationModelFinder(solverInterface) {

    protected var scopeMap: Map[Sort, Scope] = Map.empty

    def this() = this(Z3IncCliInterface, true, 1)
    override def createCompiler(): LogicCompiler = new NonExactScopeIncrementalCompiler

    def checkMonotonicity(): Map[Sort, Boolean] = {
        val typeCheckedTheory = TypecheckSanitizeTransformer(theory)
        val nnfTheory = NnfTransformer(typeCheckedTheory)
        val problemState: ProblemState = ProblemState(nnfTheory, Map.empty)
        val skolemizedPState: ProblemState = SkolemizeTransformer(problemState)
        new Monotonicity(skolemizedPState.theory).check()
    }

    def preCompile(theory: Theory, scopeMap: Map[Sort, Scope]): Theory = {
        val timeout = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
        val preCompiler: LogicCompiler = new NonExactScopePreCompiler
        preCompiler.compile(theory, scopeMap, timeout, eventLoggers.toList) match {
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
        scopeMap = if(useMonotonicity) {
            val monotonicityResult = checkMonotonicity()
            monotonicityResult.map(item => {
                item._1 -> (
                    if (item._2) ExactScope(startSize)
                    else NonExactScope(startSize)
                    )
            }).toMap
        }
        else theory.sorts.map( s => s -> NonExactScope(startSize)).toMap

        val preCompiledTheory: Theory = preCompile(theory, scopeMap)

        do {
            remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
            scopeMap = scopeMap.map(scope => {
                (scope._1 -> (
                    if (scope._2.isExact)
                        ExactScope(scope._2.size + 1)
                    else
                        NonExactScope(scope._2.size + 1)
                    ))
            }) // increase the size of each sort by 1

            println("trying scope: " + scopeMap)

            result = compiler.get.compile(preCompiledTheory, scopeMap, remainingMillis, eventLoggers.toList) match {
                case Left(CompilerError.Timeout) => TimeoutResult
                case Left(CompilerError.Other(errMsg)) => ErrorResult(errMsg)
                case Right(compilerRes) => {
                    compilerResult = Some(compilerRes)
                    val finalTheory = compilerResult.get.theory
                    notifyLoggers(_.allTransformersFinished(finalTheory, totalTimer.elapsedNano()))
                    solverPhase(finalTheory)
                }
            }
        } while (result == UnsatResult)

        result
    }


}
