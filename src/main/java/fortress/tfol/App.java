package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.util.Errors;
import java.util.List;
import java.util.ArrayList;
import fortress.tfol.visitor.TermVisitor;

//Function application f(x_1, ..., x_n)
public class App extends Term {
    private final String functionName;
    private final ImmutableList<Term> arguments;

    protected App(String functionName, ImmutableList<Term> arguments) {
        Errors.failIf(arguments.size() < 1, "Nullary function application " + functionName + " should be a Var");
        this.functionName = functionName;
        this.arguments = arguments;
    }
    
    public String getFunctionName() {
        return functionName;
    }
    
    public ImmutableList<Term> getArguments() {
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
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitApp(this);
    }
}
