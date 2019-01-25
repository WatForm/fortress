package fortress.tfol;

import fortress.util.Errors;
import java.util.List;
import java.util.ArrayList;

class Not extends Term {
    private Term body;
    
    protected Not(Term body){
        this.body = body;
    }
    
    protected Term getBody() {
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
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitNot(this);
    }
}
