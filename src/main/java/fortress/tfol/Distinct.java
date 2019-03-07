package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.util.Errors;
import fortress.tfol.operations.TermVisitor;
import java.util.List;
import java.util.ArrayList;
import java.util.function.Function;

public class Distinct extends ListOp {
    
    protected Distinct(ImmutableList<Term> arguments) {
        super(arguments);
        // Z3 allows one or more arguments
        Errors.failIf(arguments.size() < 1);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitDistinct(this);
    }
    
    public Term asPairwiseNotEquals() {
        List<Term> pairs = new ArrayList();
        int i = 0;
        int j = 0;
        for(Term ti : getArguments()) {
            i++;
            for(Term tj : getArguments()) {
                j++;
                if(i < j) {
                    pairs.add(Term.mkNot(Term.mkEq(ti, tj)));
                }
            }
        }
        return Term.mkAnd(pairs);
    }
    
    public Term mapArguments(Function<Term, ? extends Term> mapping) {
        return new Distinct(arguments.map(mapping));
    }
}
