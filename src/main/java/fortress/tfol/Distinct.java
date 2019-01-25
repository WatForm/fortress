package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

// TODO does Z3 allow distinct to have arbitrary terms in distinct?
// If so, could create a ListOp class that is a parent of AndOrList
// and Distinct

class Distinct extends Term {
    List<Var> vars;
    
    protected Distinct(List<Var> vars) {
        // TODO does z3 care if distinct has only one variable?
        Errors.failIf(vars.size() < 1);
        this.vars = vars;
    }
    
    protected List<Var> getVars() {
        return vars;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        return this.vars.equals( ((Distinct)other).vars );
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<>();
        numbers.add(vars.hashCode());
        return numbers;
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitDistinct(this);
    }
}
