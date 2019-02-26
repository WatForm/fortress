package fortress.transformers;

import fortress.tfol.*;

public interface TheoryTransformer {
    // Takes in a theory and returns a new theory
    // Guaranteed to not mutate the given theory object
    public Theory apply(Theory theory);
}
