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
        Errors.precondition(arguments.size() > 0);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitDistinct(this);
    }
    
    public Term asPairwiseNotEquals() {
        List<Term> pairs = new ArrayList<>();
        int i = 0;
        for(Term ti : getArguments()) {
            i++;
            int j = 0;
            for(Term tj : getArguments()) {
                j++;
                if(i < j) {
                    pairs.add(Term.mkNot(Term.mkEq(ti, tj)));
                }
            }
        }
        int n = getArguments().size();
        Errors.assertion(pairs.size() == (n*(n - 1) / 2), "" + n + " terms, but somehow generated " + pairs.size() + " pairs");
        return Term.mkAnd(pairs);
    }
    
    public Term mapArguments(Function<Term, ? extends Term> mapping) {
        return new Distinct(arguments.map(mapping));
    }
}
