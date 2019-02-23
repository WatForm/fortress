package fortress.tfol;

import fortress.util.Errors;
import java.util.List;
import java.util.ArrayList;
import fortress.tfol.visitor.TermVisitor;

public class Not extends Term {
    private final Term body;
    
    protected Not(Term body){
        this.body = body;
    }
    
    public Term getBody() {
        return body;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        return this.body.equals( ((Not)other).body );
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<Integer>();
        numbers.add(body.hashCode());
        return numbers;
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitNot(this);
    }
}
