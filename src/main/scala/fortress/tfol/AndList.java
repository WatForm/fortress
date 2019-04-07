package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.tfol.operations.TermVisitor;
import java.util.function.Function;

public class AndList extends AndOrList {
    protected AndList(ImmutableList<Term> arguments) {
        super(arguments);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitAndList(this);
    }
    
    public Term mapArguments(Function<Term, ? extends Term> mapping) {
        return new AndList(arguments.map(mapping));
    }
}
