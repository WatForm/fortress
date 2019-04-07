package fortress.transformers;

import fortress.tfol.*;
import fortress.util.Errors;

import java.util.Map;
import java.util.HashMap;
import java.util.List;

// Preconditions: instantiations must be to fresh variables
public class GroundingTransformer implements TheoryTransformer {
    
    private Map<Type, List<Var>> domains;
    
    public GroundingTransformer(Map<Type, List<Var>> domains) {
        Errors.precondition(allNonempty(domains), "All provided domains must be nonempty");
        Errors.precondition(! domains.keySet().contains(Type.Bool), "Bool may not be instantiated");
        this.domains = new HashMap<>(domains);
    }
    
    private static boolean allNonempty(Map<Type, List<Var>> domains) {
        return domains.values().stream().allMatch((List<Var> list) -> list.size() > 0);
    }
    
    @Override
    public Theory apply(Theory theory) {
        Errors.precondition(theory.getTypes().containsAll(domains.keySet()), "Scoped types must be within theory's types");
        
        Signature sig = theory.getSignature();
        Theory result = Theory.mkTheoryWithSignature(sig);
        
        for(Map.Entry<Type, List<Var>> instantiation : domains.entrySet()) {
            Type type = instantiation.getKey();
            List<Var> constants = instantiation.getValue();
            for(Var c : constants) {
                result = result.withConstant(c.of(type));
            }
        }
        
        for(Term axiom : theory.getAxioms()) {
            Term instantiated = axiom.recklessUnivInstantiate(domains);
            result = result.withAxiom(instantiated);
        }
        return result;
    }
    
    @Override
    public String getName() {
        return "Grounding Transformer";
    }
}
