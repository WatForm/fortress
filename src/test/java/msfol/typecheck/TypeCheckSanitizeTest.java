import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.msfol.*;
import fortress.operations.TypeCheckResult;
import java.util.List;

public class TypeCheckSanitizeTest {
    
    // Check that terms are properly sanitized during typechecking
    // Currently this just means replacing boolean = with iff
    
    @Test
    // Instances of = between booleans should be replaced with iff
    public void boolEqReplacedIff() {
        Sort A = Sort.mkSortConst("A");
        Var x = Term.mkVar("x");
        Var p = Term.mkVar("p");
        
        Signature sig = Signature.empty()
            .withSort(A)
            .withConstant(x.of(A))
            .withConstant(p.of(Sort.Bool()));
            
        Term t = Term.mkAnd(
            Term.mkEq(x, x),
            Term.mkEq(p, p)
        );
        
        Term expected = Term.mkAnd(
            Term.mkEq(x, x),
            Term.mkIff(p, p)
        );
        
        TypeCheckResult result = t.typeCheck(sig);
        assertEquals(Sort.Bool(), result.sort());
        assertEquals(expected, result.sanitizedTerm());
    }
}
    
