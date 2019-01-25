package fortress.tfol;

import fortress.util.Errors;
import java.util.List;
import java.util.ArrayList;

abstract class BinOp extends Term {
    protected Term left;
    protected Term right;
    
    protected BinOp(Term left, Term right) {
        this.left = left;
        this.right = right;
    }
    
    protected Term getLeft() {
        return left;
    }
    
    protected Term getRight() {
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
