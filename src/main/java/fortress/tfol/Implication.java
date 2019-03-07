package fortress.tfol;

import fortress.tfol.operations.TermVisitor;
import java.util.function.Function;

public class Implication extends BinOp {
    protected Implication(Term left, Term right) {
        super(left, right);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitImplication(this);
    }
    
    public Term mapArguments(Function<Term, ? extends Term> mapping) {
        return new Implication(mapping.apply(left), mapping.apply(right));
    }
}
