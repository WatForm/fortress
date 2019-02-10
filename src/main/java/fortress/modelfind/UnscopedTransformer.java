package fortress.modelfind;

import fortress.tfol.*;

public class UnscopedTransformer implements TheoryTransformer {
    public void UnscopedTransformer() {
        // Empty
    }
    
    @Override
    public Theory transform(Theory theory) {
        return theory;
    }
}
