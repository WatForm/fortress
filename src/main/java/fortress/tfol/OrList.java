package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.tfol.operations.TermVisitor;
import java.util.function.Function;

public class OrList extends AndOrList {
    protected OrList(ImmutableList<Term> arguments){
        super(arguments);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitOrList(this);
    }
    
    public Term mapArguments(Function<Term, ? extends Term> mapping) {
        return new OrList(arguments.map(mapping));
    }
}
