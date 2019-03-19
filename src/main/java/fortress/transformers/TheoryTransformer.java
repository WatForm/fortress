package fortress.transformers;

import fortress.tfol.*;

/**
* @publish
* An interface to represent an operation on a theory.
*/
public interface TheoryTransformer {
    
    /**
    @publish
    * Takes in a theory, applies some transformation to it, and produces a
    * new theory. Note that this does not mutate the theory object, only
    * produces a new one.
    */
    public Theory apply(Theory theory);
    
    public String getName();
}
