package fortress.tfol;

import fortress.tfol.visitor.TermVisitor;

public class Iff extends BinOp {
    protected Iff(Term left, Term right) {
        super(left, right);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitIff(this);
    }
}
