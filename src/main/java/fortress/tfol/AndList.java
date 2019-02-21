package fortress.tfol;

import fortress.data.ImmutableList;

class AndList extends AndOrList {
    protected AndList(ImmutableList<Term> arguments) {
        super(arguments);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitAndList(this);
    }
}
