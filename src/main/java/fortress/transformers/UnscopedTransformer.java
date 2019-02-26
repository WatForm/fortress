package fortress.transformers;

import fortress.tfol.*;

public class UnscopedTransformer implements TheoryTransformer {
    public void UnscopedTransformer() {
        // Empty
    }
    
    @Override
    public Theory apply(Theory theory) {
        return theory;
    }
}
