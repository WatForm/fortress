import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;

public class SubstitutionTest {
    
    private void assertAlphaEquivalent(Term expected, Term actual) {
        assertTrue(actual.toString() + " should be alpha equiv to " + expected.toString(),
            expected.alphaEquivalent(actual));
    }
    
    Type A = Type.mkTypeConst("A");
    
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    Var a = Term.mkVar("a");
    Var b = Term.mkVar("b");
    Var c = Term.mkVar("c");
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    
    Var _1 = Term.mkVar("_1");
    Var _2 = Term.mkVar("_2");
    
    @Test
    public void basicSubstitution() {
        Term t = Term.mkImp(p, Term.mkEq(x, Term.mkApp("f", y)));
        Term expected = Term.mkImp(p, Term.mkEq(Term.mkApp("h", z), Term.mkApp("f", y)));
        assertEquals(expected, t.substitute(x, Term.mkApp("h", z)));
    }
    
    @Test
    public void boundVar() {
        Term t1 = Term.mkAnd(Term.mkEq(x, x),
                       Term.mkExists(x.of(A), Term.mkApp("R", x)));
        Term t2 = Term.mkAnd(Term.mkEq(x, x),
                       Term.mkForall(x.of(A), Term.mkApp("R", x)));
        Term e1 = Term.mkAnd(Term.mkEq(Term.mkBottom(), Term.mkBottom()),
                      Term.mkExists(x.of(A), Term.mkApp("R", x)));
        Term e2 = Term.mkAnd(Term.mkEq(Term.mkBottom(), Term.mkBottom()),
                      Term.mkForall(x.of(A), Term.mkApp("R", x)));
        assertEquals(e1, t1.substitute(x, Term.mkBottom()));    
        assertEquals(e2, t2.substitute(x, Term.mkBottom()));    
    }
    
    @Test
    public void variableCaptureBasic() {
        Term t1 = Term.mkExists(x.of(A), Term.mkEq(x, y));
        Term t2 = Term.mkForall(x.of(A), Term.mkEq(x, y));
        
        Term e1 = Term.mkExists(_1.of(A), Term.mkEq(_1, x));
        Term e2 = Term.mkForall(_1.of(A), Term.mkEq(_1, x));
        
        Term r1 = t1.substitute(y, x);
        Term r2 = t2.substitute(y, x);
        assertAlphaEquivalent(e1, r1);
        assertAlphaEquivalent(e2, r2);
    }
    
    @Test
    @Ignore("Test not yet implemented")
    public void variableCaptureMultivarQuantifier() {
        
    }
    
    @Test
    @Ignore("Test not yet implemented")
    public void variableCaptureComplex() {
        
    }
    
}
