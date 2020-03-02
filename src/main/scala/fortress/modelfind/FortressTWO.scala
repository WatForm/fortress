package fortress.modelfind

import scala.jdk.CollectionConverters._

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._

class FortressTWO extends ModelFinder {
    
    var timeoutMilliseconds: Int = 60000
    var analysisScopes: Map[Sort, Int] = Map.empty
    var instance: Option[Interpretation] = None
    var log: java.io.Writer = new java.io.PrintWriter(new fortress.data.NullOutputStream)
    var debug: Boolean = false
    var theory: Theory = Theory.empty
    var constrainedTheory: Theory = Theory.empty
    var solverStrategy: SolverStrategy = new Z3ApiSolver
    
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
    
    def setBoundedIntegers(semantics: IntegerSemantics): Unit = {
        Errors.unsupported("Integer semnatics not supported with FortressTWO");
    }
    
    override def setDebug(enableDebug: Boolean): Unit = {
        debug = enableDebug
    }
    
    override def setOutput(logWriter: java.io.Writer) = {
        log = logWriter
    }
    
    override def checkSat(): ModelFinderResult = {
        // TODO check analysis and theory scopes consistent
        
        val timeoutNano = StopWatch.millisToNano(timeoutMilliseconds)
        
        val totalTimer = new StopWatch()
        
        val transformationTimer = new StopWatch()
        
        totalTimer.startFresh()
        
        if(theory.signature.enumConstants.nonEmpty) {
            Errors.unsupported("Enum Values not supported with FortressTWO")
        }
        
        val transformerSequence = new scala.collection.mutable.ListBuffer[TheoryTransformer]
        
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        transformerSequence += new SymmetryBreakingTransformerTWO(analysisScopes)
        transformerSequence += new DomainInstantiationTransformer(analysisScopes)
        transformerSequence += new RangeFormulaTransformerNoSymBreak(analysisScopes)
        transformerSequence += new DomainEliminationTransformer(analysisScopes)
        transformerSequence += new SimplifyTransformer
        
        def applyTransformer(transformer: TheoryTransformer, theory: Theory): Theory = {
            log.write("Applying transformer: " + transformer.name)
            log.write("... ")
            log.flush()
            transformationTimer.startFresh()
            
            val resultingTheory = transformer(theory)
            
            val elapsed = transformationTimer.elapsedNano()
            log.write(StopWatch.formatNano(elapsed) + "\n")
            resultingTheory
        }
        
        var intermediateTheory = theory
        for(transformer <- transformerSequence) {
            intermediateTheory = applyTransformer(transformer, intermediateTheory)
            
            if(totalTimer.elapsedNano() >= timeoutNano) {
                log.write("TIMEOUT within Fortress.\n")
                log.flush()
                return TimeoutResult
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
        
        log.write("Checking if solver can attempt...")
        log.flush()
        if(!solverStrategy.canAttemptSolving(intermediateTheory)) {
            log.write("solver cannot attempt.\n")
            log.flush()
            throw new java.lang.RuntimeException("Provided SolverStrategy cannot attempt to solve the theory.")
        }
        log.write("solver can attempt.\n")
        
        if(totalTimer.elapsedNano() > timeoutNano) {
            log.write("TIMEOUT within Fortress.\n")
            log.flush()
            return TimeoutResult
        }

        log.write("Invoking solver strategy...\n")
        log.flush()

        val remainingMillis = timeoutMilliseconds - StopWatch.nanoToMillis(totalTimer.elapsedNano)
        val r: ModelFinderResult = solverStrategy.solve(intermediateTheory, remainingMillis, log)
        
        log.write("Done. Result was " + r.toString + ".\n")
        
        log.write("TOTAL time: " + StopWatch.formatNano(totalTimer.elapsedNano) + "\n")
        log.flush()

        r
    }
    
    def viewModel: Interpretation = solverStrategy.getInstance(theory).viewModel(Map.empty)

    override def nextInterpretation(): ModelFinderResult = {
        val newAxiom = Not(AndList(
            viewModel.toConstraints.toList
        )).eliminateDomainElements

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
