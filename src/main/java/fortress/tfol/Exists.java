package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.tfol.visitor.TermVisitor;

public class Exists extends Quantifier {
    protected Exists(ImmutableList<AnnotatedVar> vars, Term body) {
        super(vars, body);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitExists(this);
    }
}
