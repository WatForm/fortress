package fortress.tfol;

import java.util.List;

class Forall extends Quantifier {
    protected Forall(List<Var> vars, Term body){
        super(vars, body);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitForall(this);
    }
}
