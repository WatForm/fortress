package fortress.tfol;

import java.util.List;

class Exists extends Quantifier {
    protected Exists(List<Var> vars, Term body) {
        super(vars, body);
    }
}
