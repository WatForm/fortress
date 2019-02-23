package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;
import fortress.tfol.visitor.TermVisitor;

public class Var extends Term {
    private final String name;
    
    protected Var(String name) {
        Errors.failIf(name.length() < 1);
        this.name = name;
    }
    
    public String getName() {
        return name;
    }
    
    // Shorthand for annotate(Type term)
    public AnnotatedVar of(Type type) {
        return new AnnotatedVar(this, type);
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
