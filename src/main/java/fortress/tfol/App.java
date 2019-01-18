package fortress.tfol;

import java.util.List;

//Function application f(x_1, ..., x_n)
class App extends Term {
    private FuncDecl function;
    private List<Term> arguments;

    protected App(FuncDecl function, List<Term> arguments) {
        this.function = function;
        this.arguments = arguments;
    }
}
