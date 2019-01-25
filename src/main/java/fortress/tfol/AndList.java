package fortress.tfol;

import java.util.List;

class AndList extends AndOrList {
    protected AndList(List<Term> arguments) {
        super(arguments);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitAndList(this);
    }
}
