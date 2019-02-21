package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.util.Errors;
import java.util.List;
import java.util.ArrayList;

//Function application f(x_1, ..., x_n)
class App extends Term {
    private String functionName;
    private ImmutableList<Term> arguments;

    protected App(String functionName, ImmutableList<Term> arguments) {
        this.functionName = functionName;
        this.arguments = arguments;
    }
    
    protected String getFunctionName() {
        return functionName;
    }
    
    protected ImmutableList<Term> getArguments() {
        return arguments;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        return this.functionName.equals( ((App)other).functionName )
            && this.arguments.equals( ((App)other).arguments );
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<>();
        numbers.add(functionName.hashCode());
        numbers.add(arguments.hashCode());
        return numbers;
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitApp(this);
    }
}
