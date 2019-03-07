package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;
import fortress.tfol.operations.TermVisitor;

/**
* @Publish
* Represents a syntactic variable or constant.
* Variables and constants are treated as syntactically indistinguishable;
* a Var is only considered a variable or constant depending on the signature it
* is used within.
*/
public class Var extends Term {
    
    // Published Interface
    /**
    * @Publish
    * Returns an AnnotatedVar that represents this varible annotated with the
    * given type.
    */
    public AnnotatedVar of(Type type) {
        return new AnnotatedVar(this, type);
    }
    
    // End of published interface 
    
    private final String name;
    
    protected Var(String name) {
        Errors.failIf(name.length() < 1);
        this.name = name;
    }
    
    public String getName() {
        return name;
    }
    
    
    
    @Override
    protected boolean innerEquals(Object other) {
       Errors.failIf(this.getClass() != other.getClass());
       Var o = (Var) other;
       return this.name.equals(o.name);
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<>();
        numbers.add(name.hashCode());
        return numbers;
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitVar(this);
    }
}
