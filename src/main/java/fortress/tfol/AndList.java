package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.tfol.visitor.TermVisitor;

public class AndList extends AndOrList {
    protected AndList(ImmutableList<Term> arguments) {
        super(arguments);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitAndList(this);
    }
}
