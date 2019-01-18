package fortress.tfol;

import java.util.Set;
import java.util.HashSet;

public class Theory {
    private Set<Term> axioms;
    private Set<Var> constants;
    private Set<FuncDecl> functionSymbols;
    private Set<Type> types;
    
    public Theory() {
        // TODO hash set or tree set?
        this.axioms = new HashSet<>();
        this.constants = new HashSet<>();
        this.functionSymbols = new HashSet<>();
        this.types = new HashSet<>();
        types.add(Type.Bool);
    }
    
    public void addAxiom(Term formula) {
        axioms.add(formula);
    }
    
    public Set<Term> getAxioms() {
        return axioms;
    }
}
