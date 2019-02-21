package fortress.tfol;

import fortress.data.ImmutableList;

class OrList extends AndOrList {
    protected OrList(ImmutableList<Term> arguments){
        super(arguments);
    }
    
    @Override
    protected <T> T accept(TermVisitor<T> visitor) {
        return visitor.visitOrList(this);
    }
}
