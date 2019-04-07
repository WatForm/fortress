import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.tfol.operations.TypeCheckResult;
import java.util.List;

public class TypeCheckSanitizeTest {
    
    // Check that terms are properly sanitized during typechecking
    // Currently this just means replacing boolean = with iff
    
    @Test
    // Instances of = between booleans should be replaced with iff
    public void boolEqReplacedIff() {
        Type A = Type.mkTypeConst("A");
        Var x = Term.mkVar("x");
        Var p = Term.mkVar("p");
        
        Signature sig = Signature.empty()
            .withType(A)
            .withConstant(x.of(A))
            .withConstant(p.of(Type.Bool()));
            
        Term t = Term.mkAnd(
            Term.mkEq(x, x),
            Term.mkEq(p, p)
        );
        
        Term expected = Term.mkAnd(
            Term.mkEq(x, x),
            Term.mkIff(p, p)
        );
        
        TypeCheckResult result = t.typeCheck(sig);
        assertEquals(Type.Bool(), result.type);
        assertEquals(expected, result.term);
    }
}
    
