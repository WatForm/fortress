package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._
import fortress.operations.TermOps._

abstract class TransformationModelFinder(solverSession: SolverSession)
extends ModelFinder with ModelFinderSettings {
    
    private var problemState: ProblemState = ProblemState(Theory.empty)
    // A timer to count how much total time has elapsed
    private val totalTimer: StopWatch = new StopWatch()
    
    override def checkSat(): ModelFinderResult = {
        // Restart the timer
        totalTimer.startFresh()
        
        val finalTheory: Theory = transformationPhase() match {
            case None => return TimeoutResult
            case Some(fTheory) => fTheory
        }

        val finalResult: ModelFinderResult = solverPhase(finalTheory)

        finalResult
    }
    
    protected def transformerSequence(): Seq[ProblemStateTransformer]
    
    private def applyTransformer(transformer: ProblemStateTransformer, problemState: ProblemState): ProblemState = {
        notifyLoggers(_.transformerStarted(transformer))
        val transformationTimer = new StopWatch()
        transformationTimer.startFresh()
        
        val resultingProblemState = transformer(problemState)
        
        val elapsed = transformationTimer.elapsedNano()
        notifyLoggers(_.transformerFinished(transformer, elapsed))
        resultingProblemState
    }
    
    // If times out, returns None. Otherwise, returns the final transformed theory.
    private def transformationPhase(): Option[Theory] = {
        val transformerSeq = transformerSequence()
        
        problemState = ProblemState(theory, analysisScopes)
        for(transformer <- transformerSeq) {
            problemState = applyTransformer(transformer, problemState)
            
            if(totalTimer.elapsedNano() >= timeoutNano) {
                notifyLoggers(_.timeoutInternal())
                return None
            }
        }

        notifyLoggers(_.allTransformersFinished(problemState.theory, totalTimer.elapsedNano()))
        
        if(totalTimer.elapsedNano() > timeoutNano) {
            notifyLoggers(_.timeoutInternal())
            return None
        }
        
        Some(problemState.theory)
    }
    
    // Returns the final ModelFinderResult
    private def solverPhase(finalTheory: Theory): ModelFinderResult = {
        notifyLoggers(_.invokingSolverStrategy())
        
        solverSession.close()
        solverSession.open()
        solverSession.setTheory(finalTheory)

        val remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
        
        val finalResult: ModelFinderResult = solverSession.solve(remainingMillis)
        
        notifyLoggers(_.finished(finalResult, totalTimer.elapsedNano()))
        
        finalResult
    }
    
    def viewModel: Interpretation = {
        val instance = solverSession.solution
        problemState.unapplyInterp.foldLeft(instance) {
            (interp, unapplyFn) => unapplyFn(interp)
        }
    }

    def nextInterpretation(): ModelFinderResult = {
        // Negate the current interpretation, but leave out the skolem functions
        // Different witnesses are not useful for counting interpretations
        val instance = solverSession.solution
            .withoutConstants(problemState.skolemConstants)
            .withoutFunctions(problemState.skolemFunctions)
        val newAxiom = Not(And.smart(instance.toConstraints.toList map (_.eliminateDomainElements)))
        
        problemState = ProblemState(
            problemState.theory.withAxiom(newAxiom),
            problemState.scopes,
            problemState.skolemConstants,
            problemState.skolemFunctions,
            problemState.rangeRestrictions,
            problemState.unapplyInterp
        )
        
        solverSession.close()
        solverSession.open()
        solverSession.setTheory(problemState.theory)
        solverSession.solve(timeoutMilliseconds)
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
        solverSession.close()
    }
}
