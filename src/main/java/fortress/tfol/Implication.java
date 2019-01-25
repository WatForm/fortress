package fortress.tfol;

class Implication extends BinOp {
    protected Implication(Term left, Term right) {
        super(left, right);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitImplication(this);
    }
}
