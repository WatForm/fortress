package fortress.tfol;

import fortress.util.Timer;
import fortress.util.Errors;

public class ModelFinder {
    private TheoryTransformer theoryTransformer;
    private SolverStrategy solverStrategy;
    private Timer transformationTimer;
    private Timer solverTimer;
    
    public enum Result {
        SAT, UNSAT, TIMEOUT, ERROR
    }
    
    public ModelFinder(TheoryTransformer theoryTransformer, SolverStrategy solverStrategy) {
        this.theoryTransformer = theoryTransformer;
        this.solverStrategy = solverStrategy;
        this.transformationTimer = new Timer();
        this.solverTimer = new Timer();
    }
    
    public Result findModel(Theory theory, int solverTimeout) {
        // TODO typecheck theory
        // TODO verify theory has no free variables that are not constants 
        
        transformationTimer.set();
        theoryTransformer.transformTheory(theory);
        transformationTimer.stop();
        
        solverTimer.set();
        Result r = solverStrategy.solve(theory, solverTimeout);
        solverTimer.stop();
        
        return r;
    }
}
