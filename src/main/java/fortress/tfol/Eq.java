package fortress.tfol;

class Eq extends Term {
    private Term left;
    private Term right;

    protected Eq(Term left, Term right) {
        this.left = left;
        this.right = right;
    }
}
