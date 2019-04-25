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
*/
public interface ModelFinder {
    
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
    
    public static ModelFinder createDefault() {
        return new EufSmtModelFinder(new Z3ApiSolver());
    }
    
    public void setAnalysisScope(Type t, int size);
    public void setTimeout(int milliseconds);
    public Result checkSat(Theory theory);
    public Interpretation getInstance();
    
    // Internal use only
    public void setOutput(java.io.Writer log);
    public void setDebug(boolean enableDebug);
}
