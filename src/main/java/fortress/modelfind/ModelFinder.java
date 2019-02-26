package fortress.modelfind;

import fortress.util.Timer;
import fortress.util.Errors;
import java.util.List;
import java.util.ArrayList;

import fortress.tfol.*;
import fortress.transformers.TheoryTransformer;

public class ModelFinder {
    private List<TheoryTransformer> theoryTransformers;
    private SolverStrategy solverStrategy;
    private Timer transformationTimer;
    private Timer solverTimer;
    
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
    
    public Result findModel(Theory theory, int solverTimeout) {
        
        transformationTimer.set();
        for(TheoryTransformer theoryTransformer : theoryTransformers) {
            theory = theoryTransformer.apply(theory);
        }
        transformationTimer.stop();
        
        solverTimer.set();
        Result r = solverStrategy.solve(theory, solverTimeout);
        solverTimer.stop();
        
        return r;
    }
}
