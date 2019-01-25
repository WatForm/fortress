package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

class Distinct extends Term {
    List<Var> vars;
    
    protected Distinct(List<Var> vars) {
        // TODO does z3 care if distinct has only one variable?
        Errors.failIf(vars.size() < 1);
        this.vars = vars;
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
}
