package fortress.modelfind

import fortress.tfol._
import fortress.transformers._
import fortress.util._

class EufSmtModelFinder(
    var solverStrategy: SolverStrategy,
    var timeoutMilliseconds: Int,
    var analysisScopes: Map[Type, Int],
    var instance: Option[Interpretation],
    var log: java.io.Writer,
    var debug: Boolean
) extends ModelFinder {
    
    def this(solverStrategy: SolverStrategy) = this(solverStrategy, 60000,
            Map(), None, new java.io.PrintWriter(new fortress.data.NullOutputStream), false)
    
    override def setTimeout(milliseconds: Int): Unit = {
        Errors.precondition(milliseconds >= 0)
        timeoutMilliseconds = milliseconds
    }
    
    override def setAnalysisScope(t: Type, size: Int): Unit = {
        Errors.precondition(size >= 0)
        analysisScopes = analysisScopes + (t -> size)
    }
    
    override def setDebug(enableDebug: Boolean): Unit = {
        debug = enableDebug
    }
    
    override def setOutput(logWriter: java.io.Writer) = {
        log = logWriter
    }
    
    private def usesEnumType(theory: Theory): Boolean = {
        val allFreeVarConsts = theory.axioms.map(axiom => axiom.freeVarConstSymbols).reduce( (set1, set2) => set1 union set2 )
        theory.enumConstants.exists {
            case (sort, constants) => constants.exists(c => allFreeVarConsts contains c)
        }
    }
        
    override def checkSat(theory: Theory): ModelFinder.Result = {
        // TODO check analysis and theory scopes consistent
        
        val timeoutNano = StopWatch.millisToNano(timeoutMilliseconds);
        
        val totalTimer = new StopWatch();
        
        val transformationTimer = new StopWatch();
        
        totalTimer.startFresh()
        
        val enumEliminationTransformer = new EnumEliminationTransformer
        val enumTypeMapping: Map[Var, DomainElement] = enumEliminationTransformer.computeEnumTypeMapping(theory)
        
        val rangeFormulaTransformer =
            if (usesEnumType(theory)) { new RangeFormulaTransformerNoSymBreak(analysisScopes ++ theory.scopes) }
            else { new RangeFormulaTransformerLowSymBreak(analysisScopes ++ theory.scopes) }
        
        val transformerSequence = Seq(
            enumEliminationTransformer,
            new SimplifyTransformer,
            new NnfTransformer,
            new SkolemizeTransformer,
            new DomainInstantiationTransformer(analysisScopes),
            rangeFormulaTransformer,
            new DomainEliminationTransformer(analysisScopes ++ theory.scopes),
            new SimplifyTransformer
        )
        
        def applyTransformer(transformer: TheoryTransformer, theory: Theory): Theory = {
            log.write("Applying transformer: " + transformer.getName)
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
                return ModelFinder.Result.TIMEOUT;
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
            return ModelFinder.Result.TIMEOUT
        }
        
        log.write("Invoking solver strategy...\n")
        log.flush()
        
        val remainingMillis = timeoutMilliseconds - StopWatch.nanoToMillis(totalTimer.elapsedNano)
        val r: ModelFinder.Result = solverStrategy.solve(intermediateTheory, remainingMillis, log)
        
        log.write("Done. Result was " + r.toString + ".\n")
        
        log.write("TOTAL time: " + StopWatch.formatNano(totalTimer.elapsedNano) + "\n")
        log.flush()

        r
    }
    
    def getInstance: Interpretation = ???
}
