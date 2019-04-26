package fortress.transformers;

import fortress.tfol.*;
import java.util.Set;
import java.util.HashSet;
import fortress.data.NameGenerator;
import fortress.data.SubIntNameGenerator;
import fortress.tfol.operations.ClosureEliminator;

/** Replaces transitive closure terms with a term representing the application of a new function
 but with same arguments. **/
public class ClosureEliminationTransformer implements TheoryTransformer {
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
        
        for(Term axiom : theory.getAxioms()) {
            forbiddenNames.addAll(axiom.allSymbolsJava());
        }
        
        NameGenerator nameGenerator = new SubIntNameGenerator(forbiddenNames, 0);
        
        Theory result = theory.withoutAxioms();
        for(Term axiom : theory.getAxioms()) {
            ClosureEliminator closureEliminator = new ClosureEliminator(axiom, result.getSignature(), nameGenerator);
            Term newAxiom = closureEliminator.convert();
            result = result.withFunctionDeclarations(closureEliminator.getClosureFunctions());
            result = result.withAxiom(newAxiom);
        }
        
        return result;
    }
    
    @Override
    public String getName() {
        return "Closure Elimination Transformer";
    }
}
