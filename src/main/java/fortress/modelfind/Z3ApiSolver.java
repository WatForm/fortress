package fortress.modelfind;

import java.io.*;

import fortress.tfol.*;
import fortress.outputs.*;
import fortress.util.Pair;
import fortress.util.StopWatch;
import fortress.util.Errors;

import com.microsoft.z3.*;

public class Z3ApiSolver extends SolverTemplate {
    private String lastModel = "";
    private Context context = null;
    private Solver solver = null;
    
    @Override
    public boolean canAttemptSolving(Theory theory) {
        return true;
    }
    
    @Override
    protected void convertTheory(Theory theory, Writer log) { 
        Pair<Context, Solver> pair = new TheoryToZ3Java(theory).convert();
        context = pair.left;
        solver = pair.right;
    }
    
    @Override
    protected void updateTimeout(int remainingMillis) {
        Errors.assertion(null != context);
        Errors.assertion(null != solver);
        
        Params params = context.mkParams();
        params.add("timeout", remainingMillis);
        solver.setParameters(params);
    }
    
    @Override
    protected ModelFinder.Result runSolver(Writer log) throws IOException {
        Errors.assertion(null != context);
        Errors.assertion(null != solver);
        
        Status status = solver.check();
        switch(status) {
            case UNKNOWN:
                // TODO timeout errors
                lastModel = "ERROR - NO MODEL";
                log.write("UKNOWN (" + solver.getReasonUnknown() + ").\n");
                if(solver.getReasonUnknown().equals("timeout")
                        || solver.getReasonUnknown().equals("canceled")) {
                    return ModelFinder.Result.TIMEOUT;
                }
                return ModelFinder.Result.UNKNOWN;
                // break;
            case SATISFIABLE:
                lastModel = solver.getModel().toString();
                log.write("SAT.\n");
                return ModelFinder.Result.SAT;
                // break;
            case UNSATISFIABLE:
                lastModel = "ERROR - NO MODEL";
                log.write("UNSAT.\n");
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
