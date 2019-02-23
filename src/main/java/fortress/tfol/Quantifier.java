package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.util.Errors;
import java.util.List;
import java.util.ArrayList;

public abstract class Quantifier extends Term {
    protected final ImmutableList<AnnotatedVar> vars;
    protected final Term body;
    
    protected Quantifier(ImmutableList<AnnotatedVar> vars, Term body) {
        Errors.failIf(vars.size() < 1);
        this.vars = vars;
        this.body = body;
    }
    
    public ImmutableList<AnnotatedVar> getVars() {
        return vars;
    }
    
    public Term getBody() {
        return body;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        Quantifier o = (Quantifier) other;
        return this.vars.equals(o.vars)
            && this.body.equals(o.body);
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<Integer>();
        numbers.add(vars.hashCode());
        numbers.add(body.hashCode());
        return numbers;
    }
}
