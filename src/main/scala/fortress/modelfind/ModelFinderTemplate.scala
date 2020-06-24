package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._
import fortress.operations.TermOps._

abstract class ModelFinderTemplate(solverStrategy: SolverStrategy) extends ModelFinder with ModelFinderSettings {
    private var instance: Option[Interpretation] = None
    protected var constrainedTheory: Theory = Theory.empty
    // A timer to count how much total time has elapsed
    private val totalTimer: StopWatch = new StopWatch()
    protected var enumSortMapping: Map[EnumValue, DomainElement] = Map.empty
    
    override def checkSat(): ModelFinderResult = {
        // Restart the timer
        totalTimer.startFresh()
        
        preTransformationPhase()
        
        val finalTheory: Theory = transformationPhase() match {
            case None => return TimeoutResult
            case Some(fTheory) => fTheory
        }

        val finalResult: ModelFinderResult = solverPhase(finalTheory)

        finalResult
    }
    
    protected def transformerSequence(): Seq[ProblemTransformer]
    
    private def applyTransformer(transformer: ProblemTransformer, problem: Problem): Problem = {
        for(logger <- eventLoggers) logger.transformerStarted(transformer)
        val transformationTimer = new StopWatch()
        transformationTimer.startFresh()
        
        val resultingProblem = transformer(problem)
        
        val elapsed = transformationTimer.elapsedNano()
        for(logger <- eventLoggers) logger.transformerFinished(transformer, elapsed)
        resultingProblem
    }
    
    private def preTransformationPhase(): Unit = {
        // We need to remember the enum sort mapping
        // TODO this is a little bit clunky
        enumSortMapping = (new EnumEliminationTransformer).computeEnumSortMapping(theory)
    }
    
    // If times out, returns None. Otherwise, returns the final transformed theory.
    private def transformationPhase(): Option[Theory] = {
        val transformerSeq = transformerSequence()
        
        var intermediateProblem = Problem(theory, analysisScopes)
        for(transformer <- transformerSeq) {
            intermediateProblem = applyTransformer(transformer, intermediateProblem)
            
            if(totalTimer.elapsedNano() >= timeoutNano) {
                for(logger <- eventLoggers) logger.timeoutInternal()
                return None
            }
        }
        
        val finalTheory = intermediateProblem match {
            case Problem(thry, scopes) => thry
        }

        constrainedTheory = finalTheory

        for(logger <- eventLoggers) logger.allTransformersFinished(finalTheory, totalTimer.elapsedNano())
        
        if(totalTimer.elapsedNano() > timeoutNano) {
            for(logger <- eventLoggers) logger.timeoutInternal()
            return None
        }
        
        Some(finalTheory)
    }
    
    // Returns the final ModelFinderResult
    private def solverPhase(finalTheory: Theory): ModelFinderResult = {
        for(logger <- eventLoggers) logger.invokingSolverStrategy()

        val remainingMillis = timeoutMilliseconds - totalTimer.elapsedNano().toMilli
        val finalResult: ModelFinderResult = solverStrategy.solve(finalTheory, remainingMillis, eventLoggers.toList)
        
        for(logger <- eventLoggers) logger.finished(finalResult, totalTimer.elapsedNano())
        
        finalResult
    }
    
    def viewModel: Interpretation = {
        solverStrategy.getInstance(theory)
            .applyEnumMapping(enumSortMapping.map(_.swap)) // Undo enum elimination
    }

    override def nextInterpretation(): ModelFinderResult = {
        val newAxiom = Not(AndList(
            viewModel.toConstraints.toList
        )).eliminateEnumValues(enumSortMapping).eliminateDomainElements

        //solverStrategy.addAxiom(newAxiom, timeoutMilliseconds, log)

        constrainedTheory = constrainedTheory.withAxiom(newAxiom)
        solverStrategy.solve(constrainedTheory, timeoutMilliseconds, eventLoggers.toList)
    }

    override def countValidModels(newTheory: Theory): Int = {
        theory = newTheory
        checkSat() match {
            case SatResult =>
            case UnsatResult => return 0
            case UnknownResult => Errors.solverError("Solver gave unknown result")
            case ErrorResult => Errors.solverError("An error occurred while computing result")
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
                case ErrorResult => Errors.solverError("An error occurred while computing result")
                case TimeoutResult => Errors.solverError("Solver timed out while computing result")
            }
        }

        count
    }
}
