package fortress.transformers;

import fortress.tfol.*;

/**
* A transformer that does nothing to the given theory.
* The purpose of this transformer is to make it explicit that nothing should
* be done to the theory and it should be solved as an unscoped problem.
*/
public class UnscopedTransformer implements TheoryTransformer {
    
    @Override
    public Theory apply(Theory theory) {
        return theory;
    }
    
    @Override
    public String getName() {
        return "Unscoped Transformer";
    }
}
