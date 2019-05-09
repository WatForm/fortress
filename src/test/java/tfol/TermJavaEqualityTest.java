import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;
import java.util.ArrayList;

public class TermJavaEqualityTest {
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    
    @Test
    public void distinctAsPairwiseNotEquals() {
        Distinct t1 = (Distinct) Term.mkDistinct(x, y, z); // Casting needed for this test
        Term t2 = Term.mkAnd(
            Term.mkNot(Term.mkEq(x, y)),
            Term.mkNot(Term.mkEq(x, z)),
            Term.mkNot(Term.mkEq(y, z)));
        
        assertEquals(t2, t1.asPairwiseNotEquals());
    }
}
