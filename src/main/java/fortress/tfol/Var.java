package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

public class Var extends Term {
    private String name;
    private Type type;
    
    protected Var(String name, Type type) {
        Errors.failIf(name.length() < 1);
        this.name = name;
        this.type = type;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
       Errors.failIf(this.getClass() != other.getClass());
       Var o = (Var) other;
       return this.name.equals(o.name)
           && this.type.equals(o.type);
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<>();
        numbers.add(name.hashCode());
        numbers.add(type.hashCode());
        return numbers;
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitVar(this);
    }
}
