package fortress.transformers;

import fortress.tfol.*;
import java.util.Set;
import java.util.HashSet;
import fortress.data.NameGenerator;
import fortress.data.SubIntNameGenerator;
import fortress.tfol.operations.Skolemizer;

public class SkolemizeTransformer implements TheoryTransformer {
    @Override
    public Theory apply(Theory theory) {
        Signature sig = theory.getSignature();
        Theory result = Theory.mkTheoryWithSignature(sig);
        
        Set<String> forbiddenNames = new HashSet();
        
        for(FuncDecl fdecl : theory.getFunctionDeclarations()) {
            forbiddenNames.add(fdecl.getName());
        }
        
        for(AnnotatedVar c : theory.getConstants()) {
            forbiddenNames.add(c.getName());
        }
        
        for(Term axiom : theory.getAxioms()) {
            forbiddenNames.addAll(axiom.allVarConstSymbols());
        }
        
        NameGenerator nameGenerator = new SubIntNameGenerator(forbiddenNames);
        
        for(Term axiom : theory.getAxioms()) {
            Skolemizer skolemizer = new Skolemizer(axiom, sig, nameGenerator);
            Term newAxiom = skolemizer.convert();
            result = result.withFunctionDeclarations(skolemizer.getSkolemFunctions());
            result = result.withConstants(skolemizer.getSkolemConstants());
            result = result.withAxiom(newAxiom);
        }
        
        return result;
    }
}
