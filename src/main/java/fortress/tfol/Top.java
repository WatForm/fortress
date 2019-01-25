package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

// TODO Consider making this a singleton
class Top extends Term {
    protected Top() {
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
