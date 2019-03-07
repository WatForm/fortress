package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.tfol.operations.TermVisitor;

public class Forall extends Quantifier {
    protected Forall(ImmutableList<AnnotatedVar> vars, Term body){
        super(vars, body);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitForall(this);
    }
}
