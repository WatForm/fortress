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
    var integerSemantics: IntegerSemantics = Unbounded
    
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
        integerSemantics = semantics
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
        
        val timeoutNano = StopWatch.millisToNano(timeoutMilliseconds)
        
        val totalTimer = new StopWatch()
        
        val transformationTimer = new StopWatch()
        
        totalTimer.startFresh()
        
        val enumScopes: Map[Sort, Int] = theory.signature.enumConstants.map {
            case (sort, enumValues) => sort -> enumValues.size
        }.toMap
        
        Errors.precondition(fortress.util.Maps.noConflict(enumScopes, analysisScopes))
        
        val transformerSequence = new scala.collection.mutable.ListBuffer[TheoryTransformer]
        
        val enumEliminationTransformer = new EnumEliminationTransformer
        // We need to remember the enum sort mapping
        enumSortMapping = enumEliminationTransformer.computeEnumSortMapping(theory)
        
        transformerSequence += enumEliminationTransformer
        
        integerSemantics match {
            case Unbounded => ()
            case ModularSigned(bitwidth) => {
                transformerSequence += new IntegerFinitizationTransformer(bitwidth)
            }
        }
        
        transformerSequence += new NnfTransformer
        transformerSequence += new SkolemizeTransformer
        transformerSequence += new DomainInstantiationTransformer(analysisScopes ++ enumScopes)
        transformerSequence += new RangeFormulaTransformerNoSymBreak(analysisScopes ++ enumScopes)
        transformerSequence += new DomainEliminationTransformer(analysisScopes ++ enumScopes)
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
