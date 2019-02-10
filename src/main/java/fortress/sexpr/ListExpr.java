package fortress.sexpr;

import java.util.List;
import java.util.function.Function;
import java.lang.StringBuilder;

// List expression, named to avoid conflicts with java.util.List
public class ListExpr extends SExpr {
    private List<SExpr> subexpressions;
    
    protected ListExpr(List<SExpr> subexpressions) {
        this.subexpressions = subexpressions;
    }
    
    @Override
    public <T> T match(Function<Atom, T> ifAtom, Function<ListExpr, T> ifList) {
        return ifList.apply(this);
    }
    
    @Override
    public boolean innerEquals(Object other) {
        ListExpr o = (ListExpr) other;
        return subexpressions.equals(o.subexpressions);
    }
    
    @Override
    public List<Integer> innerHashNumbers() {
        return List.of(subexpressions.hashCode());
    }
    
    @Override
    public String toString() {
        if(subexpressions.size() == 0) {
            return "()";
        }
        StringBuilder builder = new StringBuilder(subexpressions.size() * 2);
        builder.append('(');
        // First subexpression has no space before it
        boolean first = true;
        for(SExpr e : subexpressions) {
            if(!first) {
                builder.append(' ');
            }
            builder.append(e.toString());
            first = false;
        }
        builder.append(')');
        return builder.toString();
    }
}
