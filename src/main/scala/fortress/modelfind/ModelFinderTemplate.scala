package fortress.modelfind

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._

abstract class ModelFinderTemplate(var solverStrategy: SolverStrategy) extends ModelFinder {
    private var timeoutMilliseconds: Int = 60000
    protected var analysisScopes: Map[Sort, Int] = Map.empty
    private var instance: Option[Interpretation] = None
    private var log: java.io.Writer = new java.io.PrintWriter(new fortress.data.NullOutputStream)
    private var debug: Boolean = false
    protected var theory: Theory = Theory.empty
    private var constrainedTheory: Theory = Theory.empty
    protected var integerSemantics: IntegerSemantics = Unbounded
    // A timer to count how much total time has elapsed
    private val totalTimer: StopWatch = new StopWatch()
    protected var enumSortMapping: Map[EnumValue, DomainElement] = Map.empty
    protected var enumScopes: Map[Sort, Int] = Map.empty
    
    override def setTheory(newTheory: Theory): Unit = {
        theory = newTheory
    }
    
    override def setTimeout(milliseconds: Int): Unit = {
        Errors.precondition(milliseconds >= 0)
        timeoutMilliseconds = milliseconds
    }
    
    override def setAnalysisScope(t: Sort, size: Int): Unit = {
        Errors.precondition(size >= 0)
        analysisScopes = analysisScopes + (t -> size)
    }
    
    override def setBoundedIntegers(semantics: IntegerSemantics): Unit = {
        integerSemantics = semantics
    }
    
    override def setDebug(enableDebug: Boolean): Unit = {
        debug = enableDebug
    }
    
    override def setOutput(logWriter: java.io.Writer) = {
        log = logWriter
    }
    
    // Calculate the number of nanoseconds until we must output TIMEOUT
    private def timeoutNano: Long = StopWatch.millisToNano(timeoutMilliseconds)
    
    protected def transformerSequence(): Seq[TheoryTransformer]
    
    private def applyTransformer(transformer: TheoryTransformer, theory: Theory): Theory = {
        log.write("Applying transformer: " + transformer.name)
        log.write("... ")
        log.flush()
        val transformationTimer = new StopWatch()
        transformationTimer.startFresh()
        
        val resultingTheory = transformer(theory)
        
        val elapsed = transformationTimer.elapsedNano()
        log.write(StopWatch.formatNano(elapsed) + "\n")
        resultingTheory
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
        
        var intermediateTheory = theory
        for(transformer <- transformerSeq) {
            intermediateTheory = applyTransformer(transformer, intermediateTheory)
            
            if(totalTimer.elapsedNano() >= timeoutNano) {
                log.write("TIMEOUT within Fortress.\n")
                log.flush()
                return None
            }
        }

        constrainedTheory = intermediateTheory

        log.write("Total transformation time: " + StopWatch.formatNano(totalTimer.elapsedNano()) + "\n")
        log.flush()
        
        if(debug) {
            log.write("Resulting theory:\n")
            log.write(intermediateTheory.toString)
            log.write("\n")
            log.flush()
        }
        
        if(totalTimer.elapsedNano() > timeoutNano) {
            log.write("TIMEOUT within Fortress.\n")
            log.flush()
            return None
        }
        
        Some(intermediateTheory)
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
