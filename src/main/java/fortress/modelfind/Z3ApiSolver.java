package fortress.modelfind;

import java.io.*;

import fortress.tfol.*;
import fortress.tfol.operations.*;
import fortress.util.Pair;

import com.microsoft.z3.*;

public class Z3ApiSolver implements SolverStrategy {
    
    @Override
    public boolean canAttemptSolving(Theory theory) {
        return true;
    }
    
    @Override
    public ModelFinder.Result solve(Theory theory, int timeout, Writer log) throws IOException {
        log.write("Creating Z3 API solver. ");
        log.flush();
        Pair<Context, Solver> pair = new TheoryToZ3Java(theory).convert();
        Context context = pair.left;
        Solver solver = pair.right;
        
        Params params = context.mkParams();
        int milliseconds = timeout * 1000;
        params.add("timeout", milliseconds);
        solver.setParameters(params);
        
        log.write("Solving... ");
        log.flush();
        Status status = solver.check();
        
        switch(status) {
            case UNKNOWN:
                // TODO timeout errors
                return ModelFinder.Result.UNKNOWN;
                // break;
            case SATISFIABLE:
                return ModelFinder.Result.SAT;
                // break;
            case UNSATISFIABLE:
                return ModelFinder.Result.UNSAT;
                // break;
            default:
                throw new RuntimeException("Unexpected solver result " + status.toString());
        }
    }
}
