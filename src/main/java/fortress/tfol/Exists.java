package fortress.tfol;

import java.util.List;

class Exists extends Quantifier {
    protected Exists(List<AnnotatedVar> vars, Term body) {
        super(vars, body);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitExists(this);
    }
}
