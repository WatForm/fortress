package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

//Function application f(x_1, ..., x_n)
class App extends Term {
    private FuncDecl function;
    private List<Term> arguments;

    protected App(FuncDecl function, List<Term> arguments) {
        this.function = function;
        this.arguments = arguments;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        return this.function.equals( ((App)other).function )
            && this.arguments.equals( ((App)other).arguments );
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<>();
        numbers.add(function.hashCode());
        numbers.add(arguments.hashCode());
        return numbers;
    }
}
