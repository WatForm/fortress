package fortress.tfol;

import java.util.Optional;
import fortress.util.Errors;

public class TypeCheckResult {
    private Optional<Type> typeMaybe;
    // TODO add error feedback component
    
    public boolean isWellTyped() {
        return typeMaybe.isPresent();
    }
    
    public Type getType() {
        Errors.failIf(!isWellTyped());
        return typeMaybe.get();
    }
    
}
