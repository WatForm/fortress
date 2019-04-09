package fortress.transformers;

import fortress.tfol.*;

/**
* Takes a theory and produces an equivalent theory in which all formulas are in negation normal form.
*/
public class NnfTransformer implements TheoryTransformer {
    @Override
    public Theory apply(Theory theory) {
        Signature sig = theory.getSignature();
        Theory result = Theory.mkTheoryWithSignature(sig);
        
        for(Term axiom : theory.getAxioms()) {
            Term axiomPrime = axiom.nnf();
            result = result.withAxiom(axiomPrime);
        }
        
        return result;
    }
    
    @Override
    public String getName() {
        return "Negation Normal Form Transformer";
    }
}
