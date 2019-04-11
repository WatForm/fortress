package fortress.modelfind;

import fortress.tfol.*;
import java.io.Writer;
import java.io.IOException;

/**
* @publish
* An abstraction of which solving method should be used to search for a satisfying model.
* For example, dumping the theory to SMT-LIB and solving it using a command-line SMT solver.
*/

//TODO Memory out errors
public interface SolverStrategy {
    /**
    * Returns true if and only if the solver can attempt to solve the given theory.
    * For example, a SolverStrategy that invokes a SAT solver will reject a theory
    * containing quantifiers, since another TheoryTransformer should be invoked to
    * map it down into propositional logic.
    * Note that just because a solver can attempt to solve a theory does not mean
    * it will succeed.
    * For example, a SolverStrategy that invokes an SMT solver may still timeout
    * or give up partway through a solving attempt if the theory is from an
    * undecidable logic.
    */
    public boolean canAttemptSolving(Theory theory);
    
    /**
    * Attempts to solve the given theory, searching for a satisfying instance.
    */
    public ModelFinder.Result solve(Theory theory, int timeoutMillis, Writer log) throws IOException;
    
    // Temporary method -- will be changed
    public String getStringModel();

    public FiniteModel getModel(Theory theory);
}
