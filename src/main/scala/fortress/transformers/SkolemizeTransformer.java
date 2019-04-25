package fortress.transformers;

import fortress.tfol.*;
import java.util.Set;
import java.util.HashSet;
import fortress.data.NameGenerator;
import fortress.data.SubIntNameGenerator;
import fortress.tfol.operations.Skolemizer;

/**
* Takes a theory, whose formulas are all in negation normal form, and produces
* an equisatisfiable theory whose formulas are still in negation normal form and
* contain no existential quantifiers.
* Prenex normal form is preserved.
* Scopes are preserved.
*/
public class SkolemizeTransformer implements TheoryTransformer {
    @Override
    public Theory apply(Theory theory) {
        Set<String> forbiddenNames = new HashSet<>();
        
        for(Type type : theory.getTypes()) {
            forbiddenNames.add(type.getName());
        }
        
        for(FuncDecl fdecl : theory.getFunctionDeclarations()) {
            forbiddenNames.add(fdecl.getName());
        }
        
        for(AnnotatedVar c : theory.getConstants()) {
            forbiddenNames.add(c.getName());
        }
        
        // TODO: do we need this restriction if Substituter already restricts these inside one term?
        for(Term axiom : theory.getAxioms()) {
            forbiddenNames.addAll(axiom.allSymbolsJava());
        }
        
        NameGenerator nameGenerator = new SubIntNameGenerator(forbiddenNames, 0);
        
        Theory result = theory.withoutAxioms();
        for(Term axiom : theory.getAxioms()) {
            Skolemizer skolemizer = new Skolemizer(axiom, result.getSignature(), nameGenerator);
            Term newAxiom = skolemizer.convert();
            result = result.withFunctionDeclarations(skolemizer.getSkolemFunctions());
            result = result.withConstants(skolemizer.getSkolemConstants());
            result = result.withAxiom(newAxiom);
        }
        
        return result;
    }
    
    @Override
    public String getName() {
        return "Skolemize Transformer";
    }
}
