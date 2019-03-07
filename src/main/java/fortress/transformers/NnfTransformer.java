package fortress.transformers;

import fortress.tfol.*;

public class NnfTransformer implements TheoryTransformer {
    @Override
    public Theory apply(Theory theory) {
        Signature sig = theory.getSignature();
        Theory result = Theory.mkTheoryWithSignature(sig);
        
        for(Term axiom : theory.getAxioms()) {
            Term axiomPrime = axiom.nnf(sig);
            result = result.withAxiom(axiomPrime);
        }
        
        return result;
    }
}
