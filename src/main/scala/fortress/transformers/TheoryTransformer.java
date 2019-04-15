package fortress.transformers;

import fortress.tfol.*;

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
    
    public String getName();
    
    public static List<TheoryTransformer> rangeEUF(Map<Type, Integer> scopes) {
        return List.of(
            new SimplifyTransformer(),
            new NnfTransformer(),
            new SkolemizeTransformer(),
            new DomainInstantiationTransformer(scopes),
            new RangeFormulaTransformer(scopes),
            new DomainEliminationTransformer(),
            new SimplifyTransformer()
        );
    }
}
