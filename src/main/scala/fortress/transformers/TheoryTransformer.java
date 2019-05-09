package fortress.transformers;

import fortress.msfol.*;

import java.util.List;
import java.util.Map;

/**
* An abstraction of a function from Theory to Theory.
*/
public interface TheoryTransformer {
    
    /**
    * Takes in a theory, applies some transformation to it, and produces a
    * new theory. Note that this does not mutate the theory object, only
    * produces a new one.
    */
    public Theory apply(Theory theory);
    
    public String name();
}
