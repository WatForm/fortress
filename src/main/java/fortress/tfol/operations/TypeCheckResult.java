package fortress.tfol.operations;

import fortress.tfol.*;

public class TypeCheckResult {
    public Term term;
    public Type type;
    
    public TypeCheckResult(Term term, Type type) {
        this.term = term;
        this.type = type;
    }
}
