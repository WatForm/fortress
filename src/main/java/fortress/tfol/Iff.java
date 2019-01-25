package fortress.tfol;

class Iff extends BinOp {
    protected Iff(Term left, Term right) {
        super(left, right);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitIff(this);
    }
}
