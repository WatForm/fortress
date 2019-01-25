package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

// TODO Consider making this a singleton
class Bottom extends Term {
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
}
