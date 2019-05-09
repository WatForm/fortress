package fortress.solverinterface;

import java.io.*;

import fortress.msfol.*;
import fortress.outputs.*;
import fortress.util.Pair;
import fortress.util.StopWatch;
import fortress.util.Errors;

import fortress.modelfind.*;
import fortress.solverinterface.*;
import fortress.interpretation.*;

import com.microsoft.z3.*;

public class Z3ApiSolver extends SolverTemplate {
    private Model lastModel = null;
    private Context context = null;
    private Solver solver = null;
    
    @Override
    public boolean canAttemptSolving(Theory theory) {
        return true;
    }
    
    @Override
    protected void convertTheory(Theory theory, Writer log) { 
        var pair = new TheoryToZ3Java(theory).convert();
        context = pair._1();
        solver = pair._2();
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
    protected ModelFinderResult runSolver(Writer log) throws IOException {
        Errors.assertion(null != context);
        Errors.assertion(null != solver);
        
        Status status = solver.check();
        lastModel = null;
        switch(status) {
            case UNKNOWN:
                // TODO timeout errors
                log.write("UKNOWN (" + solver.getReasonUnknown() + ").\n");
                if(solver.getReasonUnknown().equals("timeout")
                        || solver.getReasonUnknown().equals("canceled")) {
                    return ModelFinderResult.Timeout();
                }
                return ModelFinderResult.Unknown();
                // break;
            case SATISFIABLE:
                lastModel = solver.getModel();
                log.write("SAT.\n");
                return ModelFinderResult.Sat();
                // break;
            case UNSATISFIABLE:
                log.write("UNSAT.\n");
                return ModelFinderResult.Unsat();
                // break;
            default:
                throw new RuntimeException("Unexpected solver result " + status.toString());
        }
    }

    public Interpretation getInstance(Theory theory) {
        Errors.assertion(null != lastModel, "There is no current instance");
        return new Z3ApiInterpretation(lastModel, theory.signature());
    }
}
