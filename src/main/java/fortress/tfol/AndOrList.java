package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.util.Errors;

// Exists as a separate subtype of ListOp since And/Or have additional commonalities
// not shared by distinct (e.g. arguments must typecheck as Bool)
public abstract class AndOrList extends ListOp {
    
    protected AndOrList(ImmutableList<Term> arguments){
        super(arguments);
        Errors.precondition(arguments.size() >= 2);
    }
    
}
