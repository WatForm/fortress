package fortress.tfol;

import fortress.data.ImmutableList;

class Exists extends Quantifier {
    protected Exists(ImmutableList<AnnotatedVar> vars, Term body) {
        super(vars, body);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitExists(this);
    }
}
