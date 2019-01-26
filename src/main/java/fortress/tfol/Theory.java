package fortress.tfol;

import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;

public class Theory {
    private Set<Term> axioms;
    private Set<Var> constants;
    private Set<FuncDecl> functionSymbols;
    private Set<Type> types;
    private Map<Type, Integer> scopes; // Optional scopes for types
    // You are allowed to have a combination of scoped and unscoped types
    
    public Theory() {
        // TODO hash set or tree set?
        this.axioms = new HashSet<>();
        this.constants = new HashSet<>();
        this.functionSymbols = new HashSet<>();
        this.types = new HashSet<>();
        this.scopes = new HashMap<>();
        types.add(Type.Bool);
    }
    
    public void addAxiom(Term formula) {
        axioms.add(formula);
    }
    
    public void addConstant(Var constant) {
        constants.add(constant);
    }
    
    public Set<Term> getAxioms() {
        return axioms;
    }
    
    public Set<Type> getTypes() {
        return types;
    }
    
    public Set<FuncDecl> getFunctionSymbols() {
        return functionSymbols;
    }
    
    public Set<Var> getConstants() {
        return constants;
    }
    
}
