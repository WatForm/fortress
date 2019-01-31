package fortress.tfol;

import java.util.Map;
import java.util.List;
import java.util.ArrayList;
import java.util.stream.Collectors;

public class NaiveScopeTransformer implements TheoryTransformer {
    public void NaiveScopeTransformer() {
        // Empty
    }
    
    @Override
    public void transformTheory(Theory theory) {
        // TODO fresh names
        Map<Type, Integer> scopes = theory.getScopes();
        scopes.forEach( (type, scope) -> {
            List<Var> variables = new ArrayList<>();
            Var x = Term.mkVar("x", type);
            for(int i = 1; i <= scope; i++) {
                Var xi = Term.mkVar(type.toString() + i, type);
                variables.add(xi);
                theory.addConstant(xi);
            }
            theory.addAxiom(Term.mkDistinct(variables));
            
            List<Term> equalityTerms = variables.stream().map(
                xi -> Term.mkEq(x, xi)
            ).collect(Collectors.toList());
            Term scopeAxiom = Term.mkForall(x, Term.mkOr(equalityTerms));
            theory.addAxiom(scopeAxiom);
        });
    }
}
