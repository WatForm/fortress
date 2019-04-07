package fortress.sexpr;

import java.util.List;
import java.util.function.Function;

public class Atom extends SExpr {
    private String value;

    protected Atom(String value) {
        this.value = value;
    }
    
    @Override
    public <T> T match(Function<Atom, T> ifAtom, Function<ListExpr, T> ifList) {
        return ifAtom.apply(this);
    }
    
    @Override
    public boolean innerEquals(Object other) {
        Atom o = (Atom) other;
        return value.equals(o.value);
    }
    
    @Override
    public List<Integer> innerHashNumbers() {
        return List.of(value.hashCode());
    }
    
    @Override
    public String toString() {
        return value;
    }
}
