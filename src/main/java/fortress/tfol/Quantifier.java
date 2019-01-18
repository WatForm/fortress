package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

abstract class Quantifier extends Term {
    protected List<Var> vars;
    protected Term body;
    
    protected Quantifier(List<Var> vars, Term body) {
        this.vars = vars;
        this.body = body;
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
