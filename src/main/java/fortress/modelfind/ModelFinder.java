package fortress.modelfind;

import fortress.util.Timer;
import fortress.util.Errors;
import java.util.List;
import java.util.ArrayList;

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
    private Timer transformationTimer;
    private Timer solverTimer;
    
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
        this.theoryTransformers = new ArrayList<>();
        this.theoryTransformers.add(theoryTransformer);
        this.solverStrategy = solverStrategy;
        this.transformationTimer = new Timer();
        this.solverTimer = new Timer();
    }
    
    public ModelFinder(List<TheoryTransformer> theoryTransformers, SolverStrategy solverStrategy) {
        this.theoryTransformers = theoryTransformers;
        this.solverStrategy = solverStrategy;
        this.transformationTimer = new Timer();
        this.solverTimer = new Timer();
    }
    
    /**
    * @publish
    * Applies the sequence of TheoryTransformers to the given theory (<i>in order</i>)
    * and attempts to solve the resultant theory using the SolverStrategy, searching for a
    * satisfying instance. Returns the result of the search.
    * Throws an exception if the SolverStrategy cannot attempt to solve the resulant theory
    * after the transformers are applied.
    */
    public Result findModel(Theory theory, int solverTimeout) {
        
        transformationTimer.set();
        for(TheoryTransformer theoryTransformer : theoryTransformers) {
            theory = theoryTransformer.apply(theory);
        }
        transformationTimer.stop();
        
        if(!solverStrategy.canAttemptSolving(theory)) {
            throw new RuntimeException("Provided SolverStrategy cannot attempt to solve the theory.");
        }
        
        solverTimer.set();
        Result r = solverStrategy.solve(theory, solverTimeout);
        solverTimer.stop();
        
        return r;
    }
}
