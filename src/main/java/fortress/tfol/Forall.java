package fortress.tfol;

import fortress.data.ImmutableList;

class Forall extends Quantifier {
    protected Forall(ImmutableList<AnnotatedVar> vars, Term body){
        super(vars, body);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitForall(this);
    }
}
