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



case class multiThreadFinderResult(modelFinderResult: ModelFinderResult, scope: Map[Sort, Scope], pid: Int) {
    override def toString: String = modelFinderResult.toString

}

abstract class RSVIncrementalModelFinder(solverInterface: SolverInterface) extends CompilationModelFinder(solverInterface) {

    var monotonicityResult: Map[Sort, Boolean] = Map.empty
    var processes: Array[ProcessSession] = new Array[ProcessSession](4)
    var liveProcess: Option[ProcessSession] = None
    var finderResult: Option[multiThreadFinderResult] = None
    var successPid: Int = -1
    override def checkMono(): java.util.Map[Sort, Boolean] = checkMonotonicity().asJava

    def checkMonotonicity(): Map[Sort, Boolean] = {
        val typeCheckedTheory = TypecheckSanitizeTransformer(theory)
        val nnfTheory = NnfTransformer(typeCheckedTheory)
        val problemState: ProblemState = ProblemState(nnfTheory, Map.empty)
        val skolemizedPState: ProblemState = SkolemizeTransformer(problemState)
        new Monotonicity(skolemizedPState.theory).check()
    }

    def sortInference(): (Theory, SortSubstitution) = {
        val typeCheckedTheory = TypecheckSanitizeTransformer(theory)
        val (generalTheory, sortSubstitution) = typeCheckedTheory.inferSorts
        (generalTheory, sortSubstitution)
    }

    /*
        method = 0/1/2/3
        method = 0:  Monotonicity checking + RSVIncrementalSolving
        method = 1: RSVIncrementalSolving
        method = 2: Non-exact Scope solving (size = 5, 6, 7...)
        method = 3: Monotonicity checking + Non-exact Scope Solving
     */
    def checkSatByPid(pid: Int): multiThreadFinderResult = {
        var newTheory: Theory = theory
        var scopeMap: Map[Sort, Scope] = theory.sorts.map(s => s -> ExactScope(1)).toMap
        if (pid == 0) {
            val MMS: MergeMonotonicSorts = new MergeMonotonicSorts(theory.sorts.filter(monotonicityResult(_)))
            newTheory = MMS.updateTheory(theory)
            scopeMap = newTheory.sorts.map(s => s -> ExactScope(1)).toMap
        }
        if (pid == 2) {
            scopeMap = theory.sorts.map(s => s -> NonExactScope(1)).toMap
        }
        if (pid == 3) {
//            val MMS: MergeMonotonicSorts = new MergeMonotonicSorts(theory.sorts.filter(monotonicityResult(_)))
//            newTheory = MMS.updateTheory(theory)
            scopeMap = {
                monotonicityResult.map(item => {
                    item._1 -> (
                        if(item._2) ExactScope(1)
                        else NonExactScope(1)
                    )
                }).toMap
            }
        }
        solve(newTheory, scopeMap, pid)
    }

    def solve(t: Theory, s: Map[Sort, Scope], pid: Int): multiThreadFinderResult = {
        var scopeMap = s
        var result: ModelFinderResult = UnsatResult
        var unsatCore: String = ""
        var ret: (ModelFinderResult, String) = null

        totalTimer.startFresh()
        compiler = Some(createCompiler())
        var remainingMillis = timeoutMilliseconds

        if (pid == 2 || pid == 3) { // non-exact scope
            val compiler1 = {
                if(!scopeMap.values.forall(s => s.isExact)) new PredUpperBoundCompiler
                else new FortressTHREECompiler
            }
            do {
                remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
                scopeMap = scopeMap.map(scope => {
                    (scope._1 -> (
                        if(scope._2.isExact)
                            ExactScope(scope._2.size + 1)
                        else
                            NonExactScope(scope._2.size + 1)
                    ))
                }) // increase the size of each sort by 1
                result = compiler1.compile(t, scopeMap, remainingMillis, eventLoggers.toList) match {
                    case Left(CompilerError.Timeout) => TimeoutResult
                    case Left(CompilerError.Other(errMsg)) => ErrorResult(errMsg)
                    case Right(compilerRes) => {
                        compilerResult = Some(compilerRes)
                        val finalTheory = compilerResult.get.theory
                        notifyLoggers(_.allTransformersFinished(finalTheory, totalTimer.elapsedNano()))
                        ret = solveByZ3(finalTheory, pid)
                        ret._1
                    }
                }
            } while (result == UnsatResult)
        }

        else {
            do {
                result = {
                    remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
                    compiler.get.compile(t, scopeMap, remainingMillis, eventLoggers.toList) match {
                        case Left(CompilerError.Timeout) => TimeoutResult
                        case Left(CompilerError.Other(errMsg)) => ErrorResult(errMsg)
                        case Right(compilerRes) => {
                            compilerResult = Some(compilerRes)
                            val finalTheory = compilerResult.get.theory
                            notifyLoggers(_.allTransformersFinished(finalTheory, totalTimer.elapsedNano()))
                            ret = solveByZ3(finalTheory, pid)
                            unsatCore = ret._2
                            ret._1
                        }
                    }
                }
                if (result == UnsatResult) {
                    val constraints: Seq[String] = unsatCore.substring(1, unsatCore.length - 1).split(" ")
                    if (constraints.nonEmpty && constraints.head != "") {
                        for (con <- constraints) {
                            val sort: Sort = SortConst(con.split("_").head)
                            scopeMap += (sort -> ExactScope(scopeMap(sort).size + 1))
                        }
                    }
//                    println("trying scope: " + scopeMap)
                }
            } while (result == UnsatResult)
        }
        multiThreadFinderResult(result, scopeMap, pid)
    }

    def solveByZ3(theory: Theory, pid: Int): (ModelFinderResult, String) = {
        if (processes(pid) != null) processes(pid).close()
        if (finderResult.nonEmpty) return null
        processes(pid) = new ProcessSession(Seq("z3", "-smt2", "-in").asJava)
        processes(pid).write("(set-option :produce-models true)\n")
        processes(pid).write("(set-option :produce-unsat-cores true)\n")
        processes(pid).write("(set-option :smt.core.minimize true)\n")
        processes(pid).write("(set-logic ALL)\n")
        val converter = new SmtlibConverter(writer = processes(pid).inputWriter)
        converter.writeTheory(theory)
        val (result, elapsedSolverNano) = measureTime {
            val remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
            if (remainingMillis.value > 0) {
                processes(pid).write(s"(set-option :timeout ${remainingMillis.value})")
                processes(pid).write("(check-sat)\n")
                processes(pid).flush()
                val ret = processes(pid).readLine()
                ret match {
                    case "sat" => ModelFinderResult.Sat
                    case "unsat" => ModelFinderResult.Unsat
                    case "Unknown" => {
                        processes(pid).write("(get-info :reason-unknown)\n")
                        processes(pid).flush()
                        val reason: String = processes(pid).readLine()
                        if (reason.contains("timeout")) ModelFinderResult.Timeout
                        else ModelFinderResult.Unknown
                    }
                    case _ => ErrorResult(s"Unrecognized result '${ret}'")
                }
            }
            else TimeoutResult
        }

        var unsat_core: String = ""
        if (result == UnsatResult) {
            processes(pid).write("(get-unsat-core)\n")
            processes(pid).flush()
            unsat_core = processes(pid).readLine()
        }

        (result, unsat_core)
    }

    case class task(pid: Int) extends Callable[multiThreadFinderResult] {
        override def call(): multiThreadFinderResult = checkSatByPid(pid)

    }

    override def multiThreadCheckSat(): ModelFinderResult = {
        monotonicityResult = checkMonotonicity()
        val executorService = Executors.newFixedThreadPool(4)
        val tasks: java.util.ArrayList[Callable[multiThreadFinderResult]] = new util.ArrayList[Callable[multiThreadFinderResult]]()
        tasks.add(task(0))
        tasks.add(task(1))
        tasks.add(task(2))
        tasks.add(task(3))
        finderResult = Some(executorService.invokeAny(tasks))
        executorService.shutdownNow()
        successPid = finderResult.get.pid // get process id real solve the problem
        liveProcess = Some(processes(successPid)) // get the process
        for(i <- 0 to 3 if processes(i)!= null) processes(i).close() // close other processes
        println("successPid: " + successPid)
        for(i <- 0 to 3) {
            if (processes(i)!= null)
                println("process " + i + ": " + processes(i).isAlive)
            else println("process " + i + " is null")
        }
        finderResult.get.modelFinderResult
    }



    def getScope(rawScope: Map[Sort, Scope]): Map[Sort, Scope] = successPid match {
        case 0 => {
            if(rawScope.contains(SortConst("MONO"))) {
                val mono: Int = rawScope(SortConst("MONO")).size
                val nonMonoScopes: Map[Sort, Scope] = rawScope.filter(s => monotonicityResult.contains(s._1))
                val monoScopes: Map[Sort, Scope] = monotonicityResult.filter(_._2).map(_._1 -> ExactScope(mono))
                nonMonoScopes ++ monoScopes
            }
            else rawScope
        }
        case 1 => rawScope
        // TODO: unapply result of non-exact scope solving
        case 2 => rawScope
        case 3 => rawScope
        case _ => Errors.Internal.impossibleState("Impossible pid.")
    }


    def getModel: String = {
        Errors.Internal.assertion(liveProcess.nonEmpty, "Cannot get model without a live process")
        var model: String = ""
        liveProcess.get.write("(get-model)\n")
        liveProcess.get.flush()
        var line: String = liveProcess.get.readLine()
        while ( {
            line = liveProcess.get.readLine();
            line != ")"
        }) {
            model ++= line + "\n"
        }
        model
    }

    override def viewModel: Interpretation = ???

    override def checkSat(): ModelFinderResult = this.multiThreadCheckSat()

    override def checkSat(method: Int): ModelFinderResult = {
        monotonicityResult = checkMonotonicity()
        checkSatByPid(method).modelFinderResult
    }


}

