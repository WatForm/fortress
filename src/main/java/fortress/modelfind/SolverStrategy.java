package fortress.modelfind;

import fortress.tfol.*;

interface SolverStrategy {
    public ModelFinder.Result solve(Theory theory, int timeout);
}
