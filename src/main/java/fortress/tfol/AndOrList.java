package fortress.tfol;

import java.util.List;

// Exists as a separate subtype of ListOp since And/Or have additional commonalities
// not shared by distinct (e.g. arguments must typecheck as Bool)
abstract class AndOrList extends ListOp {
    
    protected AndOrList(List<Term> arguments){
        super(arguments);
    }
    
}
