package fortress.modelfind;

import java.util.Map;
import java.util.List;
import java.util.ArrayList;
import java.util.stream.Collectors;

import fortress.tfol.*;

public abstract class NaiveScopeTransformer implements TheoryTransformer {
    public void NaiveScopeTransformer() {
        // Empty
    }
    
    // @Override
    // public void transformTheory(Theory theory) {
    //     // TODO fresh names
    //     Map<Type, Integer> scopes = theory.getScopes();
    //     scopes.forEach( (type, scope) -> {
    //         List<AnnotatedVar> variables = new ArrayList<>();
    //         AnnotatedVar x = Term.mkAnnotatedVar("x", type);
    //         for(int i = 1; i <= scope; i++) {
    //             AnnotatedVar xi = Term.mkAnnotatedVar(type.toString() + i, type);
    //             variables.add(xi);
    //             theory.addConstant(xi);
    //         }
    // 
    //         theory.addAxiom(Term.mkDistinct(variables.stream().map(av -> av.getVar()).collect(Collectors.toList())));
    // 
    //         List<Term> equalityTerms = variables.stream().map(
    //             xi -> Term.mkEq(x.getVar(), xi.getVar())
    //         ).collect(Collectors.toList());
    //         Term scopeAxiom = Term.mkForall(x, Term.mkOr(equalityTerms));
    //         theory.addAxiom(scopeAxiom);
    //     });
    // }
}