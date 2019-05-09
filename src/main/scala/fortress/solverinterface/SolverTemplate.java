package fortress.solverinterface;

import fortress.msfol.*;
import fortress.util.StopWatch;
import fortress.modelfind.*;

import java.io.Writer;
import java.io.IOException;

abstract class SolverTemplate implements SolverStrategy {
    
    @Override
    public ModelFinderResult solve(Theory theory, int timeoutMillis, Writer log) throws IOException {
        // template method
        
        log.write("Converting to solver format: ");
        log.flush();
        
        StopWatch conversionTimer = new StopWatch();
        conversionTimer.startFresh();
        
        convertTheory(theory, log);
        
        log.write(StopWatch.formatNano(conversionTimer.elapsedNano()) + "\n");
        log.flush();
        
        
        int remainingMillis = timeoutMillis - StopWatch.nanoToMillis(conversionTimer.elapsedNano());
        if(remainingMillis <= 0) {
            log.write("TIMEOUT within Fortress.\n");
            log.flush();
            return ModelFinderResult.Timeout();
        }
        
        updateTimeout(remainingMillis);
        
        log.write("Solving... ");
        log.flush();
        
        StopWatch solverTimer = new StopWatch();
        solverTimer.startFresh();
        
        ModelFinderResult result = runSolver(log);
        
        log.write("Z3 solver time: " + StopWatch.formatNano(solverTimer.elapsedNano()) + "\n");
        
        return result;
    }
    
    abstract protected void convertTheory(Theory theory, Writer log) throws IOException;
    abstract protected void updateTimeout(int remainingMillis);
    abstract protected ModelFinderResult runSolver(Writer log) throws IOException;
}
