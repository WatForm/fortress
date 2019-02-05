package fortress.tfol;

// NOTE: does not extend Term
public class AnnotatedVar {
    private Var variable;
    private Type type;
    
    protected AnnotatedVar(Var variable, Type type) {
        this.variable = variable;
        this.type = type;
    }
    
    protected Type getType() {
        return type;
    }
    
    protected Var getVar() {
        return variable;
    }
    
    protected String getName() {
        return variable.getName();
    }
    
    @Override
    public boolean equals(Object other) {
        if(this == other) {
            return true;
        }
        if(null == other) {
            return false;
        }
        if(this.getClass() != other.getClass()) {
            return false;
        }
        
        AnnotatedVar o = (AnnotatedVar) other;
        return this.variable.equals(o.variable)
            && this.type.equals(o.type);
    }
    
    @Override
    public int hashCode() {
        int prime = 31;
        int result = 1;
        result = result * prime + variable.hashCode();
        result = result * prime + type.hashCode();
        return result;
    }
}
