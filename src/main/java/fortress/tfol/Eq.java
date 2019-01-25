package fortress.tfol;

class Eq extends BinOp {
    protected Eq(Term left, Term right) {
        super(left, right);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitEq(this);
    }
}
