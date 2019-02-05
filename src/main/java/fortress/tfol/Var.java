package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

public class Var extends Term {
    private String name;
    
    protected Var(String name) {
        Errors.failIf(name.length() < 1);
        this.name = name;
    }
    
    protected String getName() {
        return name;
    }
    
    public AnnotatedVar annotate(Type term) {
        return new AnnotatedVar(this, term);
    }
    
    // Shorthand for annotate(Type term)
    public AnnotatedVar of(Type type) {
        return annotate(type);
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
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitVar(this);
    }
}
