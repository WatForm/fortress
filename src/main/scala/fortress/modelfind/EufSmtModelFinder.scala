package fortress.modelfind

import scala.collection.JavaConverters._

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._
import fortress.solverinterface._

class EufSmtModelFinder(var solverStrategy: SolverStrategy) extends ModelFinder {
    
    var timeoutMilliseconds: Int = 60000
    var analysisScopes: Map[Sort, Int] = Map.empty
    var instance: Option[Interpretation] = None
    var log: java.io.Writer = new java.io.PrintWriter(new fortress.data.NullOutputStream)
    var debug: Boolean = false
    var theory: Theory = Theory.empty
    var enumSortMapping: Map[EnumValue, DomainElement] = Map.empty
    
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
    
    override def setDebug(enableDebug: Boolean): Unit = {
        debug = enableDebug
    }
    
    override def setOutput(logWriter: java.io.Writer) = {
        log = logWriter
    }
    
    private def usesEnumSort(theory: Theory): Boolean = theory.axioms.exists(_.allEnumValues.nonEmpty)
    
    override def checkSat(): ModelFinderResult = {
        // TODO check analysis and theory scopes consistent
        
        val timeoutNano = StopWatch.millisToNano(timeoutMilliseconds);
        
        val totalTimer = new StopWatch();
        
        val transformationTimer = new StopWatch();
        
        totalTimer.startFresh()
        
        val enumScopes: Map[Sort, Int] = theory.signature.enumConstants.map {
            case (sort, enumValues) => sort -> enumValues.size
        }.toMap
        
        Errors.precondition(fortress.util.Maps.noConflict(enumScopes, analysisScopes))
        
        val enumEliminationTransformer = new EnumEliminationTransformer
        enumSortMapping = enumEliminationTransformer.computeEnumSortMapping(theory)
        
        val transformerSequence = Seq(
            enumEliminationTransformer,
            new SimplifyTransformer,
            new NnfTransformer,
            new SkolemizeTransformer,
            new DomainInstantiationTransformer(analysisScopes ++ enumScopes),
            new RangeFormulaTransformerNoSymBreak(analysisScopes ++ enumScopes),
            new DomainEliminationTransformer(analysisScopes ++ enumScopes),
            new SimplifyTransformer
        )
        
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
                log.write("TIMEOUT within Fortress.\n");
                log.flush();
                return TimeoutResult;
            }
        }
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
    
    def viewModel: Interpretation = solverStrategy.getInstance(theory).viewModel(enumSortMapping.map(_.swap))
}
