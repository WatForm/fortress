package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.tfol.operations.TermVisitor;
import java.util.function.Function;

public class Forall extends Quantifier {
    protected Forall(ImmutableList<AnnotatedVar> vars, Term body){
        super(vars, body);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitForall(this);
    }
    
    public Term mapBody(Function<Term, ? extends Term> mapping) {
        return new Forall(vars, mapping.apply(body));
    }
}
