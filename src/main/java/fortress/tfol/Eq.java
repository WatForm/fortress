package fortress.tfol;

import fortress.tfol.visitor.TermVisitor;

public class Eq extends BinOp {
    protected Eq(Term left, Term right) {
        super(left, right);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitEq(this);
    }
}
