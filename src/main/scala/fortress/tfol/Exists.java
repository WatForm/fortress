package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.tfol.operations.TermVisitor;
import java.util.function.Function;

public class Exists extends Quantifier {
    protected Exists(ImmutableList<AnnotatedVar> vars, Term body) {
        super(vars, body);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitExists(this);
    }
    
    public Term mapBody(Function<Term, ? extends Term> mapping) {
        return new Exists(vars, mapping.apply(body));
    }
}
