package fortress.sexpr;

import java.util.List;
import java.util.ArrayList;
import fortress.util.SimpleEquals;
import java.util.function.Function;

public abstract class SExpr implements SimpleEquals {
    
    public static SExpr mkAtom(String value) {
        return new Atom(value);
    }
    
    public static SExpr mkList(List<SExpr> subexpressions) {
        return new ListExpr(subexpressions);
    }
    
    public static SExpr mkList(SExpr... subexpressions) {
        List<SExpr> sub = new ArrayList();
        for(SExpr e : subexpressions) {
            sub.add(e);
        }
        return mkList(sub);
    }
    
    public abstract <T> T match(Function<Atom, T> ifAtom, Function<ListExpr, T> ifList);
    
    @Override
    public boolean equals(Object other) {
        return SimpleEquals.equal(this, other);
    }
    
    @Override
    public int hashCode() {
        return SimpleEquals.hashCode(this);
    }
    
    public abstract String toString();
}
