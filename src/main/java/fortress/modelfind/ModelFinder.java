package fortress.modelfind;

import fortress.util.StopWatch;
import fortress.util.Errors;

import java.util.List;
import java.util.ArrayList;
import java.io.OutputStream;
import java.io.Writer;
import java.io.PrintWriter;
import java.io.IOException;
import fortress.data.NullOutputStream;

import fortress.tfol.*;
import fortress.transformers.TheoryTransformer;

/**
* @publish
* An object that is invoked to search for satisfying models to theories.
* It is parameterized by a sequence of TheoryTransformers, which are applied
* to the theory before solving is attempted, and a SolverStrategy, which determines
* how the ModelFinder attempts to solve the theory (e.g. using a specific SMT solver).
*/
public class ModelFinder {
    private List<TheoryTransformer> theoryTransformers;
    private SolverStrategy solverStrategy;
    private StopWatch transformationTimer;
    private StopWatch solverTimer;
    
    /**
    * @publish
    * The various return possibilities of the model finder.
    * SAT means the theory is satisfiable.
    * UNSAT means the theory is unsatisfiable.
    * TIMEOUT means the model finder could not be determined within the time limit.
    * UNKNOWN means the satisfiability of the theory could not be determined for another reason,
    * such as the underlying solver giving up, which is valid behaviour in undecidable logics.
    * ERROR means there was a fatal problem; this is not expected behaviour.
    */
    public enum Result {
        SAT, UNSAT, UNKNOWN, TIMEOUT, ERROR
    }
    
    
    public ModelFinder(TheoryTransformer theoryTransformer, SolverStrategy solverStrategy) {
        this(List.of(theoryTransformer), solverStrategy);
    }
    
    public ModelFinder(List<TheoryTransformer> theoryTransformers, SolverStrategy solverStrategy) {
        this.theoryTransformers = theoryTransformers;
        this.solverStrategy = solverStrategy;
        this.transformationTimer = new StopWatch();
        this.solverTimer = new StopWatch();
    }
    
    /**
    * @publish
    * Applies the sequence of TheoryTransformers to the given theory (<i>in order</i>)
    * and attempts to solve the resultant theory using the SolverStrategy, searching for a
    * satisfying instance. Returns the result of the search.
    * Throws an exception if the SolverStrategy cannot attempt to solve the resulant theory
    * after the transformers are applied.
    */
    public Result findModel(Theory theory, int solverTimeout) throws IOException {
        return findModel(theory, solverTimeout, new PrintWriter(new NullOutputStream()), false);
    }
    
    public Result findModel(Theory theory, int solverTimeout, Writer log, boolean debug) throws IOException {
        
        long totalElapsedTransform = 0;
        for(TheoryTransformer theoryTransformer : theoryTransformers) {
            log.write("Applying transformer: " + theoryTransformer.getName());
            log.write("... ");
            log.flush();
            transformationTimer.startFresh();
            
            theory = theoryTransformer.apply(theory);
            
            long elapsed = transformationTimer.stop();
            totalElapsedTransform += elapsed;
            log.write(StopWatch.format(elapsed) + "\n");
        }
        log.write("Total transformation time: " + StopWatch.format(totalElapsedTransform) + "\n");
        log.flush();
        
        if(debug) {
            log.write("Resulting theory:\n");
            log.write(theory.toString());
            log.write("\n");
            log.flush();
        }
        
        log.write("Checking if solver can attempt...");
        log.flush();
        if(!solverStrategy.canAttemptSolving(theory)) {
            log.write("solver cannot attempt.\n");
            log.flush();
            throw new RuntimeException("Provided SolverStrategy cannot attempt to solve the theory.");
        }
        log.write("solver can attempt.\n");
        
        log.write("Attempting to solve...\n");
        log.flush();
        solverTimer.startFresh();
        Result r = solverStrategy.solve(theory, solverTimeout, log);
        long elapsedSolver = solverTimer.stop();
        log.write("Done. Result was " + r.toString() + ".\n");
        log.write("Solving time: " + StopWatch.format(elapsedSolver) + "\n");
        log.write("TOTAL time: " + StopWatch.format(totalElapsedTransform + elapsedSolver) + "\n");
        log.flush();

        return r;
    }
}
