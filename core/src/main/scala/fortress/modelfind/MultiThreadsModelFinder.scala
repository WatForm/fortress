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



case class MultiThreadFinderResult(modelFinderResult: ModelFinderResult, modelFinder: ModelFinder) {
    override def toString: String = modelFinderResult.toString

}

class MultiThreadsModelFinder(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {

    var processes: Array[ProcessSession] = new Array[ProcessSession](3)
    var finderResult: Option[MultiThreadFinderResult] = None
    var successModelFinder: Option[ModelFinder] = None

    override def createCompiler(): LogicCompiler = null

    def checkMonotonicity(): Map[Sort, Boolean] = {
        val typeCheckedTheory = TypecheckSanitizeTransformer(theory)
        val nnfTheory = NnfTransformer(typeCheckedTheory)
        val problemState: ProblemState = ProblemState(nnfTheory, Map.empty)
        val skolemizedPState: ProblemState = SkolemizeTransformer(problemState)
        new Monotonicity(skolemizedPState.theory).check()
    }


    case class task(modelFinder: ModelFinder) extends Callable[MultiThreadFinderResult] {
        override def call(): MultiThreadFinderResult = {
            modelFinder.setTheory(theory)
            val result = modelFinder.checkSat()
            MultiThreadFinderResult(result, modelFinder)
        }
    }

    /*
        method = 0: RSVIncrementalSolving
        method = 1: Merge monotonic sorts + RSVIncrementalSolving
        method = 2: Non-exact Scope solving
        method = 3: Exact scope for monotonic sorts + Non-exact Scope Solving
     */
    def multiThreadCheckSat(): ModelFinderResult = {
        val executorService = Executors.newFixedThreadPool(3)
        val tasks: java.util.ArrayList[Callable[MultiThreadFinderResult]] = new util.ArrayList[Callable[MultiThreadFinderResult]]()
        val task0 = task(new RSVIncrementalModelFinder(Z3IncCliInterface, false))
        val task1 = task(new RSVIncrementalModelFinder(Z3IncCliInterface, true))
        val task3 = task(new NonExactScopeIncrementalModelFinder(Z3IncCliInterface, true, 1))
        tasks.add(task0)
        tasks.add(task1)
        tasks.add(task3)
        finderResult = Some(executorService.invokeAny(tasks))
        executorService.shutdownNow()

        if(task0.modelFinder != finderResult.get.modelFinder) task0.modelFinder.close()
        if(task1.modelFinder != finderResult.get.modelFinder) task1.modelFinder.close()
        if(task3.modelFinder != finderResult.get.modelFinder) task3.modelFinder.close()

        successModelFinder = Some(finderResult.get.modelFinder)
        finderResult.get.modelFinderResult
    }


    override def checkSat(): ModelFinderResult = this.multiThreadCheckSat()

    override def viewModel: Interpretation = successModelFinder.get.viewModel()

    override def nextInterpretation(): ModelFinderResult = successModelFinder.get.nextInterpretation()

//    override def countValidModels(newTheory: Theory): Int = successModelFinder.get.countValidModels()

}

