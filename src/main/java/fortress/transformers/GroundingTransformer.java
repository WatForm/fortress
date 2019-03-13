package fortress.transformers;

import fortress.tfol.*;
import java.util.Map;
import java.util.List;

// Preconditions: instantiations must be to fresh variables
public class GroundingTransformer implements TheoryTransformer {
    
    private Map<Type, List<Var>> typeInstantiations;
    
    public GroundingTransformer(Map<Type, List<Var>> typeInstantiations) {
        this.typeInstantiations = typeInstantiations;
    }
    
    @Override
    public Theory apply(Theory theory) {
        Signature sig = theory.getSignature();
        Theory result = Theory.mkTheoryWithSignature(sig);
        
        for(Map.Entry<Type, List<Var>> instantiation : typeInstantiations.entrySet()) {
            Type type = instantiation.getKey();
            List<Var> constants = instantiation.getValue();
            for(Var c : constants) {
                result = result.withConstant(c.of(type));
            }
        }
        
        for(Term axiom : theory.getAxioms()) {
            Term instantiated = axiom.univInstantiate(typeInstantiations);
            result = result.withAxiom(instantiated);
        }
        return result;
    }
}
