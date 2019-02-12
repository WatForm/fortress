package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

class Distinct extends ListOp {
    
    protected Distinct(List<Term> arguments) {
        super(arguments);
        // Z3 allows one or more arguments
        Errors.failIf(arguments.size() < 1);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitDistinct(this);
    }
}
