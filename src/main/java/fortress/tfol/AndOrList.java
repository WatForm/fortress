package fortress.tfol;

import fortress.data.ImmutableList;

// Exists as a separate subtype of ListOp since And/Or have additional commonalities
// not shared by distinct (e.g. arguments must typecheck as Bool)
abstract class AndOrList extends ListOp {
    
    protected AndOrList(ImmutableList<Term> arguments){
        super(arguments);
    }
    
}
