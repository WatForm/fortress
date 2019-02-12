package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

abstract class ListOp extends Term {
    private List<Term> arguments;
    
    protected ListOp(List<Term> arguments) {
        this.arguments = arguments;
    }
    
    protected List<Term> getArguments() {
        return arguments;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        return this.arguments.equals( ((ListOp) other).arguments );
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<>();
        numbers.add(arguments.hashCode());
        return numbers;
    }
}
