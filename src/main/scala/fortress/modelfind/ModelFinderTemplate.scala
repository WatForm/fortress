package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._

abstract class ModelFinderTemplate(var solverStrategy: SolverStrategy) extends ModelFinder with StdModelFindConfig {
    private var instance: Option[Interpretation] = None
    private var constrainedTheory: Theory = Theory.empty
    // A timer to count how much total time has elapsed
    private val totalTimer: StopWatch = new StopWatch()
    protected var enumSortMapping: Map[EnumValue, DomainElement] = Map.empty
    protected var enumScopes: Map[Sort, Int] = Map.empty
    
    override def checkSat(): ModelFinderResult = {
        // Restart the timer
        totalTimer.startFresh()
        
        preTransformationPhase()
        
        val finalTheory: Theory = transformationPhase(theory) match {
            case None => return TimeoutResult
            case Some(fTheory) => fTheory
        }

        val finalResult: ModelFinderResult = solverPhase(finalTheory)

        finalResult
    }
    
    protected def transformerSequence(): Seq[ProblemTransformer]
    
    private def applyTransformer(transformer: ProblemTransformer, problem: Problem): Problem = {
        log.write("Applying transformer: " + transformer.name)
        log.write("... ")
        log.flush()
        val transformationTimer = new StopWatch()
        transformationTimer.startFresh()
        
        val resultingProblem = transformer(problem)
        
        val elapsed = transformationTimer.elapsedNano()
        log.write(StopWatch.formatNano(elapsed) + "\n")
        resultingProblem
    }
    
    private def preTransformationPhase(): Unit = {
        // Compute the scopes for enum sorts
        enumScopes = theory.signature.enumConstants.map {
            case (sort, enumValues) => sort -> enumValues.size
        }.toMap
        
        // Check there is no conflict between the enum scopes and the analysis scopes
        Errors.precondition(fortress.util.Maps.noConflict(enumScopes, analysisScopes))
        
        // We need to remember the enum sort mapping
        // TODO this is a little bit clunky
        enumSortMapping = (new EnumEliminationTransformer).computeEnumSortMapping(theory)
    }
    
    // If times out, returns None. Otherwise, returns the final transformed theory.
    private def transformationPhase(theory: Theory): Option[Theory] = {
        val transformerSeq = transformerSequence()
        
        var intermediateProblem = Problem(theory, Map.empty)
        for(transformer <- transformerSeq) {
            intermediateProblem = applyTransformer(transformer, intermediateProblem)
            
            if(totalTimer.elapsedNano() >= timeoutNano) {
                log.write("TIMEOUT within Fortress.\n")
                log.flush()
                return None
            }
        }
        
        val finalTheory = intermediateProblem match {
            case Problem(thry, scopes) => thry
        }

        constrainedTheory = finalTheory

        log.write("Total transformation time: " + StopWatch.formatNano(totalTimer.elapsedNano()) + "\n")
        log.flush()
        
        if(debug) {
            log.write("Resulting theory:\n")
            log.write(finalTheory.toString)
            log.write("\n")
            log.flush()
        }
        
        if(totalTimer.elapsedNano() > timeoutNano) {
            log.write("TIMEOUT within Fortress.\n")
            log.flush()
            return None
        }
        
        Some(finalTheory)
    }
    
    // Returns the final ModelFinderResult
    private def solverPhase(finalTheory: Theory): ModelFinderResult = {
        log.write("Invoking solver strategy...\n")
        log.flush()

        val remainingMillis = timeoutMilliseconds - StopWatch.nanoToMillis(totalTimer.elapsedNano)
        val finalResult: ModelFinderResult = solverStrategy.solve(finalTheory, remainingMillis, log)
        
        log.write("Done. Result was " + finalResult.toString + ".\n")
        
        log.write("TOTAL time: " + StopWatch.formatNano(totalTimer.elapsedNano) + "\n")
        log.flush()
        
        finalResult
    }
    
    def viewModel: Interpretation = solverStrategy.getInstance(theory).viewModel(enumSortMapping.map(_.swap))

    override def nextInterpretation(): ModelFinderResult = {
        val newAxiom = Not(AndList(
            viewModel.toConstraints.toList
        )).eliminateEnumValues(enumSortMapping).eliminateDomainElements

        //solverStrategy.addAxiom(newAxiom, timeoutMilliseconds, log)

        constrainedTheory = constrainedTheory.withAxiom(newAxiom)
        solverStrategy.solve(constrainedTheory, timeoutMilliseconds, log)
    }

    override def countValidModels(newTheory: Theory): Int = {
        theory = newTheory
        checkSat() match {
            case SatResult =>
            case UnsatResult => return 0
            case UnknownResult =>
                log.write("Solver gave unknown result\n")
                log.flush()
                return 0
            case ErrorResult =>
                log.write("An error occurred while computing result\n")
                log.flush()
                return 0
            case TimeoutResult =>
                log.write("Solver timed out while computing result\n")
                log.flush()
                return 0
        }

        var count: Int = 1

        var sat: Boolean = true
        while (sat) {
            val r: ModelFinderResult = nextInterpretation()

            r match {
                case SatResult => count += 1
                case UnsatResult => sat = false
                case UnknownResult =>
                    log.write("Solver gave unknown result\n")
                    log.flush()
                    sat = false
                case ErrorResult =>
                    log.write("An error occurred while computing result\n")
                    log.flush()
                    sat = false
                case TimeoutResult =>
                    log.write("Solver timed out while computing result\n")
                    log.flush()
                    sat = false
            }
        }

        count
    }
}
