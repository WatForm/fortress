package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.util.Errors;
import java.util.ArrayList;
import java.util.List;

// TODO consider renaming

public abstract class ListOp extends Term {
    private final ImmutableList<Term> arguments;
    
    protected ListOp(ImmutableList<Term> arguments) {
        this.arguments = arguments;
    }
    
    public ImmutableList<Term> getArguments() {
        return arguments;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        return this.arguments.equals( ((ListOp) other).arguments );
    }
    
    @Override
    public List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<>();
        numbers.add(arguments.hashCode());
        return numbers;
    }
}
