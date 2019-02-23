package fortress.tfol;

// TODO: is there any reason for Annotated Var to contain a var object and
// not just the name? Can make annoying to decide whether to check by names
// or variable equality etc. Should just be one option for simplicity.
// On the other hand I can also see some cases it might be less work to have two options.

// NOTE: does not extend Term
public class AnnotatedVar {
    private final Var variable;
    private final Type type;
    
    protected AnnotatedVar(Var variable, Type type) {
        this.variable = variable;
        this.type = type;
    }
    
    public Type getType() {
        return type;
    }
    
    public Var getVar() {
        return variable;
    }
    
    public String getName() {
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
