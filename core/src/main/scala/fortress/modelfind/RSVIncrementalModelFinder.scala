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

abstract class RSVIncrementalModelFinder(solverInterface: SolverInterface)
extends ModelFinder
with ModelFinderSettings {
    private val totalTimer: StopWatch = new StopWatch()
    private var compiler: Option[LogicCompiler] = None
    private var solverSession: Option[solver] = None
    private var compilerResult: Option[CompilerResult] = None

    protected def createCompiler(): LogicCompiler

    override def checkSat(): ModelFinderResult = {
        totalTimer.startFresh()
        compiler =  Some(createCompiler())

        compiler.get.compile(theory, analysisScopes, timeoutMilliseconds, eventLoggers.toList) match {
            case
        }

        ???
    }

    override def countValidModels(newTheory: Theory): Int = ???

    override def viewModel(): Interpretation = ???

    override def nextInterpretation(): ModelFinderResult = ???

    override def close(): Unit = ???
}
