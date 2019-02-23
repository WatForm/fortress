package fortress.tfol;

import fortress.util.Errors;
import java.util.List;
import java.util.ArrayList;

public abstract class BinOp extends Term {
    protected final Term left;
    protected final Term right;
    
    protected BinOp(Term left, Term right) {
        this.left = left;
        this.right = right;
    }
    
    public Term getLeft() {
        return left;
    }
    
    public Term getRight() {
        return right;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        return this.left.equals( ((BinOp)other).left )
            && this.right.equals( ((BinOp)other).right );
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<>();
        numbers.add(left.hashCode());
        numbers.add(right.hashCode());
        return numbers;
    }
}
