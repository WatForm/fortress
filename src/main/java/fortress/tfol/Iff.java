package fortress.tfol;

class Iff extends Term {
    private Term left;
    private Term right;
    
    protected Iff(Term left, Term right) {
        this.left = left;
        this.right = right;
    }
}
