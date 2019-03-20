package fortress.transformers;

import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;
import java.util.stream.Collectors;

import fortress.tfol.*;
import fortress.data.NameGenerator;
import fortress.data.SubIntNameGenerator;
import fortress.data.CartesianProduct;

/**
* @publish
* A transformation that instantiates universal quantifiers and adds finite range formulas.
* The theory must not contain any existential quantifiers (e.g. it is Skolemized).
* This transformation is parameterized by a mapping from types to sizes, called scopes.
* The resulting theory will be satisfiable if and only if the original theory
* has a satisfying model that respects these scopes.
*/
public class RangeFormulaTransformer implements TheoryTransformer {
    private Map<Type, Integer> scopes;
    
    public RangeFormulaTransformer(Map<Type, Integer> scopes) {
        this.scopes = new HashMap(scopes); // Copy
    }
    
    @Override
    public Theory apply(Theory theory) {
        
        // TODO could make this name forbidding more efficient if make it a method of theory
        // and have theory keep track of all names it uses
        
        Set<String> forbiddenNames = new HashSet();
        
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
            forbiddenNames.addAll(axiom.allSymbols());
        }
        
        NameGenerator nameGen = new SubIntNameGenerator(forbiddenNames, 1);
        
        Map<Type, List<Var>> generatedUniverse = generateUniverse(nameGen);
        
        List<Term> distinctUniverseElements = new ArrayList<>();
        for(List<Var> domainElementsOfTypeT : generatedUniverse.values()) {
            distinctUniverseElements.add(Term.mkDistinct(domainElementsOfTypeT));
        }
        
        List<Term> rangeFormulas = generateRangeFormulas(theory, generatedUniverse);
        
        Theory result = new GroundingTransformer(generatedUniverse).apply(theory)
            .withAxioms(distinctUniverseElements)
            .withAxioms(rangeFormulas);
        
        return result;
    }
    
    private Map<Type, List<Var>> generateUniverse(NameGenerator nameGen) {
        Map<Type, List<Var>> universe = new HashMap();
        for(Map.Entry<Type, Integer> scope : scopes.entrySet()) {
            Type type = scope.getKey();
            int size = scope.getValue();
            List<Var> vars = new ArrayList<>();
            for(int i = 0; i < size; i++) {
                String name = nameGen.freshName(type.getName().toLowerCase());
                vars.add(Term.mkVar(name));
            }
            universe.put(type, vars);
        }
        return universe;
    }
    
    private List<Term> generateRangeFormulas(Theory theory, Map<Type, List<Var>> generatedUniverse) {
        List<Term> rangeConstraints = new ArrayList<>();
        
        // Generate range constraints for constants, with symmetry breaking
        // Track how many far up we've gone for each type in symmetry breaking
        Map<Type, Integer> symmetryDepth = new HashMap();
        for(Type type : generatedUniverse.keySet()) {
            symmetryDepth.put(type, 0);
        }
        for(AnnotatedVar av : theory.getConstants()) {
            Type type = av.getType();
            Var c = av.getVar();
            
            List<Var> univForType = generatedUniverse.get(type);
            // The number of equalities c = a_i to disjunct is either however
            // many equalities we made for the last constant of this type plus one,
            // or the total number of universe constants of this type,
            // whichever is smaller
            int numEqualities = Math.min(symmetryDepth.get(type) + 1, univForType.size());
            symmetryDepth.put(type, numEqualities);
            
            List<Term> equalities = new ArrayList<>(numEqualities);
            for(int i = 0; i < numEqualities; i++) {
                equalities.add(Term.mkEq(c, generatedUniverse.get(type).get(i)));
            }
            
            Term disjunction = Term.mkOr(equalities);
            rangeConstraints.add(disjunction);
        }
        
        // TODO implement symmetry breaking
        // Generate range constraints for functions, without symmetry breaking
        for(FuncDecl f : theory.getFunctionDeclarations()) {
            // Skip predicates
            if(f.getResultType().equals(Type.Bool)) {
                continue;
            }
            
            // if f: A_1 x ... x A_n -> B
            // and each A_i has generated domain S_i
            // get the list [S_1, ..., S_n] and take the cartesian product
            List<List<Var>> toProduct = new ArrayList<>();
            for(Type type : f.getArgTypes()) {
                toProduct.add(generatedUniverse.get(type));
            }
            CartesianProduct<Var> argumentLists = new CartesianProduct(toProduct);
            for(List<Var> argumentList : argumentLists) {
                Term f_args = Term.mkApp(f.getName(), argumentList);
                
                // Generate f(args) = b_1 OR f(args) = b_2 OR ...
                List<Term> equalities = new ArrayList<>();
                for(Var b : generatedUniverse.get(f.getResultType())) {
                    equalities.add(Term.mkEq(f_args, b));
                }
                rangeConstraints.add(Term.mkOr(equalities));
            }
        }
        return rangeConstraints;
    }
    
    @Override
    public String getName() {
        return "RangeFormulaTransformer";
    }
}
