package fortress.tfol;

import java.util.List;

abstract class Quantifier extends Term {
    protected List<Var> vars;
    protected Term body;
    
    protected Quantifier(List<Var> vars, Term body) {
        this.vars = vars;
        this.body = body;
    }
}
