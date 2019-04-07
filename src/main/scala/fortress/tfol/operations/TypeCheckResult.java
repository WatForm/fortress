package fortress.tfol.operations;

import fortress.tfol.*;

public class TypeCheckResult {
    public Term term;
    public Type type;
    public boolean containsConnectives;
    public boolean containsQuantifiers;
    
    public TypeCheckResult(Term term, Type type, boolean containsConnectives, boolean containsQuantifiers) {
        this.term = term;
        this.type = type;
        this.containsConnectives = containsConnectives;
        this.containsQuantifiers = containsQuantifiers;
    }
}
