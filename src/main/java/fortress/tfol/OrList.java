package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.tfol.visitor.TermVisitor;

public class OrList extends AndOrList {
    protected OrList(ImmutableList<Term> arguments){
        super(arguments);
    }
    
    @Override
    public <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitOrList(this);
    }
}
