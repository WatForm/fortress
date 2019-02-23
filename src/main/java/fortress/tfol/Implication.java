package fortress.tfol;

import fortress.tfol.visitor.TermVisitor;

public class Implication extends BinOp {
    protected Implication(Term left, Term right) {
        super(left, right);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitImplication(this);
    }
}
