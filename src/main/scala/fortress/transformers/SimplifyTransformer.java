package fortress.transformers;

import fortress.tfol.*;

public class SimplifyTransformer implements TheoryTransformer {
    @Override
    public Theory apply(Theory theory) {
        Signature sig = theory.getSignature();
        Theory result = Theory.mkTheoryWithSignature(sig);
        
        for(Term axiom : theory.getAxioms()) {
            Term axiomPrime = axiom.simplify();
            result = result.withAxiom(axiomPrime);
        }
        
        return result;
    }
    
    @Override
    public String getName() {
        return "Simplify Transformer";
    }
}