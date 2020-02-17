import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.msfol.*;
import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;

public class SubstitutionTest {
    
    private void assertAlphaEquivalent(Term expected, Term actual) {
        assertTrue(expected.toString() + "\n should be alpha equiv to the actual \n" + actual.toString(),
            expected.alphaEquivalent(actual));
    }
    
    Sort A = Sort.mkSortConst("A");
    Sort B = Sort.mkSortConst("B");
    
    Var w = Term.mkVar("w");
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
        
        Term e1 = Term.mkExists(z.of(A), Term.mkEq(z, x));
        Term e2 = Term.mkForall(z.of(A), Term.mkEq(z, x));
        
        Term r1 = t1.substitute(y, x);
        Term r2 = t2.substitute(y, x);
        assertAlphaEquivalent(e1, r1);
        assertAlphaEquivalent(e2, r2);
    }
    
    @Test
    public void variableCaptureMultivarQuantifier() {
        Term t1 = Term.mkExists(List.of(x.of(A), y.of(B)), Term.mkApp("P", x, y, z));
        Term t2 = Term.mkForall(List.of(x.of(A), y.of(B)), Term.mkApp("P", x, y, z));
        
        Term expected1 = Term.mkExists(List.of(x.of(A), w.of(B)), Term.mkApp("P", x, w, y));
        Term expected2 = Term.mkForall(List.of(w.of(A), y.of(B)), Term.mkApp("P", w, y, x));
        
        assertAlphaEquivalent(expected1, t1.substitute(z, y));
        assertAlphaEquivalent(expected2, t2.substitute(z, x));
    }
    
    @Test
    public void variableCaptureComplex() {
        Term t = Term.mkOr(
            Term.mkForall(x.of(A), Term.mkAnd(
                Term.mkApp("Q", x),
                Term.mkExists(x.of(A), Term.mkApp("P", x, y)))),
            Term.mkApp("Q", y));
        
        Term expected = Term.mkOr(
            Term.mkForall(z.of(A), Term.mkAnd(
                Term.mkApp("Q", z),
                Term.mkExists(w.of(A), Term.mkApp("P", w, x)))),
            Term.mkApp("Q", x));
        
        assertAlphaEquivalent(expected, t.substitute(y, x));
    }
    
}
