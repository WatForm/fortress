package fortress.tfol;

import fortress.tfol.visitor.TermVisitor;
import java.util.function.Function;

public class Iff extends BinOp {
    protected Iff(Term left, Term right) {
        super(left, right);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitIff(this);
    }
    
    public Term mapArguments(Function<Term, ? extends Term> mapping) {
        return new Iff(mapping.apply(left), mapping.apply(right));
    }
}
