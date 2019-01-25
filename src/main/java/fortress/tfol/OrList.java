package fortress.tfol;

import java.util.List;

class OrList extends AndOrList {
    protected OrList(List<Term> arguments){
        super(arguments);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitOrList(this);
    }
}
