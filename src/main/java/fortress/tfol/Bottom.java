package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;
import fortress.tfol.operations.TermVisitor;

// TODO Consider making this a singleton
public class Bottom extends Term {
    protected Bottom() {
        // Empty
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        return true;
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        // TODO this implementaton might not be ideal
        return new ArrayList<Integer>();
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitBottom(this);
    }
}
