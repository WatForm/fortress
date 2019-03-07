package fortress.transformers;

import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;

import fortress.tfol.*;

/**
* @publish
* A transformation that instantiates universal quantifiers and adds finite range formulas.
* The theory must not contain any existential quantifiers (e.g. it is Skolemized).
* This transformation is parameterized by a mapping from types to sizes, called scopes.
* The resulting theory will be satisfiable if and only if the original theory
* had a satisfying model that respects these scopes.
*/
public abstract class RangeFormulaTransformer implements TheoryTransformer {
    private Map<Type, Integer> scopes;
    
    public RangeFormulaTransformer(Map<Type, Integer> scopes) {
        this.scopes = new HashMap(scopes); // Copy
    }
    
    // TODO implement
    @Override
    public Theory apply(Theory theory) {
        return theory;
    }
    
    // @Override
    // public void transformTheory(Theory theory) {
    //     // TODO fresh names
    //     Map<Type, Integer> scopes = theory.getScopes();
    //     scopes.forEach( (type, scope) -> {
    //         // Generate universe of given type
    //         // TODO make this separate function, possibly in another class
    //         // to avoid duplication
    //         List<AnnotatedVar> universeVars = new ArrayList<>();
    //         AnnotatedVar x = Term.mkAnnotatedVar("x", type);
    //         for(int i = 1; i <= scope; i++) {
    //             AnnotatedVar ei = Term.mkAnnotatedVar(type.toString() + i, type);
    //             universeVars.add(ei);
    //             theory.addConstant(ei);
    //         }
    //         theory.addAxiom(Term.mkDistinct(universeVars.stream().map(av -> av.getVar()).collect(Collectors.toList())));
    // 
    //         // Restrict constant values
    //         for(AnnotatedVar c : theory.getConstants()) {
    //             if (c.getType().equals(type)) {
    //                 List<Term> equalityTerms = universeVars.stream().map(
    //                     ei -> Term.mkEq(x.getVar(), ei.getVar())
    //                 ).collect(Collectors.toList());
    //                 Term rangeAxiom = Term.mkOr(equalityTerms);
    //                 theory.addAxiom(rangeAxiom);
    //             }
    //         }
    // 
    //         // Restrict output values of functions
    //         for(FuncDecl f : theory.getFunctionDeclarations()) {
    //             if(f.getResultType().equals(type)) {
    //                 List<AnnotatedVar> domainVars = new ArrayList<>();
    //                 List<Type> domainTypes = f.getArgTypes();
    //                 for(int i = 0; i < domainTypes.size(); i++) {
    //                     AnnotatedVar xi = Term.mkAnnotatedVar("x" + (i + 1), domainTypes.get(i));
    //                     domainVars.add(xi);
    //                 }
    // 
    //                 // f(x_1, ..., x_m) = e_1 or ... or f(x_1, ..., x_m) = e_n
    //                 // TODO should we allow covariance to avoid this copying?
    //                 List<Term> domainVarUses = new ArrayList<Term>(domainVars.stream().map(av -> av.getVar()).collect(Collectors.toList()));
    //                 List<Term> equalityTerms = universeVars.stream().map(
    //                     ei -> Term.mkEq(Term.mkApp(f.getName(), domainVarUses), ei.getVar())
    //                 ).collect(Collectors.toList());
    // 
    //                 Term rangeAxiom = Term.mkForall(domainVars, Term.mkOr(equalityTerms));
    //                 theory.addAxiom(rangeAxiom);
    //             }
    //         }
    //     });
    // }
}
