package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

class TypeConst extends Type {
    private String name;
    
    protected TypeConst(String name) {
        this.name = name;
    }
    
    @Override
    protected boolean innerEquals(Object other) {
        Errors.failIf(this.getClass() != other.getClass());
        return this.name.equals( ((TypeConst)other).name );
    }
    
    @Override
    protected List<Integer> innerHashNumbers() {
        List<Integer> numbers = new ArrayList<Integer>();
        numbers.add(name.hashCode());
        return numbers;
    }
}
