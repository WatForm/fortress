package fortress.transformers;

import fortress.tfol.*;

import java.util.List;
import java.util.Map;

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
    
    public static List<TheoryTransformer> rangeEUF(Map<Type, Integer> scopes) {
        return List.of(
            new SimplifyTransformer(),
            new NnfTransformer(),
            new SkolemizeTransformer(),
            new GroundRangeFormulaTransformer(scopes),
            new SimplifyTransformer()
        );
    }
}
