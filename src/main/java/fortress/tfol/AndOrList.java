package fortress.tfol;

import java.util.List;

abstract class AndOrList extends Term {
    protected List<Term> arguments;
    
    protected AndOrList(List<Term> arguments){
        this.arguments = arguments;
    }
}
