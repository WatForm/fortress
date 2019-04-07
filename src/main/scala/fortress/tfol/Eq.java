package fortress.tfol;

import fortress.tfol.operations.TermVisitor;
import java.util.function.Function;

public class Eq extends BinOp {
    protected Eq(Term left, Term right) {
        super(left, right);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitEq(this);
    }
    
    public Term mapArguments(Function<Term, ? extends Term> mapping) {
        return new Eq(mapping.apply(left), mapping.apply(right));
    }
}
