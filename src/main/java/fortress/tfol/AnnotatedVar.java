package fortress.tfol;

// TODO: is there any reason for Annotated Var to contain a var object and
// not just the name? Can make annoying to decide whether to check by names
// or variable equality etc. Should just be one option for simplicity.
// On the other hand I can also see some cases it might be less work to have two options.

/**
* @Publish
* Represents a variable together with a type annotation.
* This is used, for example, when quantifying a variable
* (as type annotations are required in quantifiers), or when declaring
* a variable to be a constant of a given type.
* Note that AnnotatedVar is not a subclass of Term.
* Fortress does not allow variables to be annotated when used as terms.
* This is to avoid silly errors such as "forall x: A, p(x:B)".
* Inside a term it is only possible (and in fact required) to annotate variables
* where a quantifier declares it bound.
*/
public class AnnotatedVar {
    
    // No published interface
    
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
