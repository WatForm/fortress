package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._
import fortress.operations.TermOps._
import fortress.compiler._

abstract class CompilationModelFinder(solverInterface: SolverInterface)
extends ModelFinder
with ModelFinderSettings {
    
    // private var problemState: ProblemState = ProblemState(Theory.empty)
    // A timer to count how much total time has elapsed
    private val totalTimer: StopWatch = new StopWatch()
    private var compiler: Option[LogicCompiler] = None
    private var solverSession: Option[SolverSession] = None
    private var compilerResult: Option[CompilerResult] = None

    protected def createCompiler(integerSemantics: IntegerSemantics): LogicCompiler
    
    override def checkSat(): ModelFinderResult = {
        // Restart the timer
        totalTimer.startFresh()

        compiler = Some(createCompiler(integerSemantics))

        val result = compiler.get.compile(theory, analysisScopes, timeoutMilliseconds) match {
            case Left(error) => ???
            case Right(result) => result
        }

        compilerResult = Some(result)
        
        val finalTheory = compilerResult.get.theory

        val finalResult: ModelFinderResult = solverPhase(finalTheory)

        finalResult
    }
    
    // Returns the final ModelFinderResult
    private def solverPhase(finalTheory: Theory): ModelFinderResult = {
        notifyLoggers(_.invokingSolverStrategy())
        
        // Close solver session, if one exists
        solverSession.foreach(_.close())
        
        // Open new solver session
        val session = solverInterface.openSession()
        solverSession = Some(session)
        session.setTheory(finalTheory)

        val remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
        
        val finalResult: ModelFinderResult = session.solve(remainingMillis)
        
        notifyLoggers(_.finished(finalResult, totalTimer.elapsedNano()))
        
        finalResult
    }
    
    def viewModel: Interpretation = {
        val instance = solverSession.get.solution
        compilerResult.get.decompileInterpretation(instance)
        // problemState.unapplyInterp.foldLeft(instance) {
        //     (interp, unapplyFn) => unapplyFn(interp)
        // }
    }

    def nextInterpretation(): ModelFinderResult = {
        // Negate the current interpretation, but leave out the skolem functions
        // Different witnesses are not useful for counting interpretations
        val instance = solverSession.get.solution
            .withoutDeclarations(compilerResult.get.skipForNextInterpretation)
            // .withoutConstants(problemState.skolemConstants)
            // .withoutFunctions(problemState.skolemFunctions)
        val newAxiom = Not(And.smart(instance.toConstraints.toList map (_.eliminateDomainElements)))
        
        solverSession.get.addAxiom(newAxiom)
        solverSession.get.solve(timeoutMilliseconds)
    }

    override def countValidModels(newTheory: Theory): Int = {
        theory = newTheory
        checkSat() match {
            case SatResult =>
            case UnsatResult => return 0
            case UnknownResult => Errors.solverError("Solver gave unknown result")
            case ErrorResult(_) => Errors.solverError("An error occurred while computing result")
            case TimeoutResult => Errors.solverError("Solver timed out while computing result")
        }

        var count: Int = 1

        var sat: Boolean = true
        while (sat) {
            val r: ModelFinderResult = nextInterpretation()

            r match {
                case SatResult => count += 1
                case UnsatResult => sat = false
                case UnknownResult => Errors.solverError("Solver gave unknown result")
                case ErrorResult(_) => Errors.solverError("An error occurred while computing result")
                case TimeoutResult => Errors.solverError("Solver timed out while computing result")
            }
        }

        count
    }
    
    override def close(): Unit = {
        solverSession.foreach(_.close())
    }
}
