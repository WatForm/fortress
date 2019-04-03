package fortress.modelfind;

import java.io.*;

import fortress.tfol.*;
import fortress.outputs.*;
import fortress.util.Pair;
import fortress.util.StopWatch;

import com.microsoft.z3.*;

public class Z3ApiSolver implements SolverStrategy {
    private String lastModel = "";
    
    @Override
    public boolean canAttemptSolving(Theory theory) {
        return true;
    }
    
    @Override
    public ModelFinder.Result solve(Theory theory, int timeoutMillis, Writer log) throws IOException {
        log.write("Creating Z3 API solver: ");
        log.flush();
        
        StopWatch conversionTimer = new StopWatch();
        conversionTimer.startFresh();
        
        Pair<Context, Solver> pair = new TheoryToZ3Java(theory).convert();
        Context context = pair.left;
        Solver solver = pair.right;
        
        log.write(StopWatch.formatNano(conversionTimer.elapsedNano()) + "\n");
        log.flush();
        
        Params params = context.mkParams();
        int remainingMillis = timeoutMillis - StopWatch.nanoToMillis(conversionTimer.elapsedNano());
        if(remainingMillis <= 0) {
            log.write("TIMEOUT within Fortress.\n");
            log.flush();
            return ModelFinder.Result.TIMEOUT;
        }
        params.add("timeout", remainingMillis);
        solver.setParameters(params);
        
        log.write("Solving... ");
        log.flush();
        
        StopWatch solverTimer = new StopWatch();
        solverTimer.startFresh();
        
        Status status = solver.check();
        
        
        switch(status) {
            case UNKNOWN:
                // TODO timeout errors
                lastModel = "ERROR - NO MODEL";
                log.write("UKNOWN (" + solver.getReasonUnknown() + ").\n");
                log.write("Z3 solver time: " + StopWatch.formatNano(solverTimer.elapsedNano()) + "\n");
                if(solver.getReasonUnknown().equals("timeout")) {
                    return ModelFinder.Result.TIMEOUT;
                }
                return ModelFinder.Result.UNKNOWN;
                // break;
            case SATISFIABLE:
                lastModel = solver.getModel().toString();
                log.write("SAT.\n");
                log.write("Z3 solver time: " + StopWatch.formatNano(solverTimer.elapsedNano()) + "\n");
                return ModelFinder.Result.SAT;
                // break;
            case UNSATISFIABLE:
                lastModel = "ERROR - NO MODEL";
                log.write("UNSAT.\n");
                log.write("Z3 solver time: " + StopWatch.formatNano(solverTimer.elapsedNano()) + "\n");
                return ModelFinder.Result.UNSAT;
                // break;
            default:
                throw new RuntimeException("Unexpected solver result " + status.toString());
        }
    }
    
    // Temporary method -- will be changed
    public String getStringModel() {
        return lastModel;
    }
}
