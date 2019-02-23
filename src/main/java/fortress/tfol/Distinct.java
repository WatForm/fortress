package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.util.Errors;
import fortress.tfol.visitor.TermVisitor;

public class Distinct extends ListOp {
    
    protected Distinct(ImmutableList<Term> arguments) {
        super(arguments);
        // Z3 allows one or more arguments
        Errors.failIf(arguments.size() < 1);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitDistinct(this);
    }
}
