import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import static fortress.tfol.Term.*;
import static fortress.tfol.Type.*;
import static fortress.tfol.FuncDecl.*;
import java.util.List;
import java.util.ArrayList;

public class TermJavaEqualityTest {
    
    // TODO do we want p & r is equal to r & p?
    // What about forall x y . P(x), forall y x . P(x)?
    // I don't think we should treat forall x . p(x), forall y . p(y) as equal
    // -- they are equivalent, but not syntactically identical
    // Equals is for testing purposes -- does it help or hurt us?

    // These tests are fairly rudimentary since it is difficult to test
    // thoroughly but the implementation is straighforward

    Type A = mkTypeConst("A");
    Var a1 = mkVar("a1");
    Var a2 = mkVar("a2");
    Var a3 = mkVar("a3");
    Var x = mkVar("x");
    Var y = mkVar("y");
    Var z = mkVar("z");
    
    Term p = mkVar("p");
    Term q = mkVar("q");
    Term r = mkVar("r");
    
    @Test
    public void FuncDeclaration() {
        FuncDecl p1 = mkFuncDecl("p", A, Bool);
        List<Type> argTypes = new ArrayList<>();
        argTypes.add(A);
        FuncDecl p2 = mkFuncDecl("p", argTypes, Bool);
        FuncDecl p3 = mkFuncDecl("pp", A, Bool);
        FuncDecl p4 = mkFuncDecl("p", Bool, Bool);
        
        assertEquals(p1, p2);
        assertNotEquals(p1, p3);
        assertNotEquals(p1, p4);
    }
    
    @Test
    public void TopBottom() {
        assertEquals(Term.mkTop(), Term.mkTop());
        assertEquals(Term.mkBottom(), Term.mkBottom());
        assertNotEquals(Term.mkTop(), Term.mkBottom());
    }

    @Test
    public void And() {
        assertEquals(mkAnd(p, q), mkAnd(p, q));
        assertNotEquals(mkAnd(p, q), mkAnd(p, r));
    }
    
    @Test
    public void Or() {
        assertEquals(mkOr(p, q), mkOr(p, q));
        assertNotEquals(mkOr(p, q), mkOr(p, r));
    }
    
    @Test
    public void Imp() {
        assertEquals(mkImp(p, q), mkImp(p, q));
        assertNotEquals(mkImp(p, q), mkImp(p, r));
    }
    
    @Test
    public void Eq() {
        assertEquals(mkEq(a1, a2), mkEq(a1, a2));
        assertNotEquals(mkEq(a1, a2), mkEq(a1, a3));
    }
    
    @Test
    public void App() {
        List<Term> a1List = new ArrayList<>();
        a1List.add(a1);
        assertEquals(mkApp("P", a1), mkApp("P", a1List));
        assertNotEquals(mkApp("P", a1), mkApp("P", a2));
        assertNotEquals(mkApp("P", a1), mkApp("Q", a1));
    }
    
    @Test
    public void Forall() {
        List<AnnotatedVar> xList = new ArrayList<>();
        xList.add(x.of(A));
        assertEquals(mkForall(x.of(A), mkApp("P", x)), mkForall(xList, mkApp("P", x)));
        assertNotEquals(mkForall(x.of(A), mkApp("P", x)), mkForall(y.of(A), mkApp("P", x)));
        assertNotEquals(mkForall(x.of(A), mkApp("P", x)), mkForall(x.of(A), mkApp("Q", x)));
        assertNotEquals(mkForall(x.of(A), mkApp("P", x)), mkForall(y.of(A), mkApp("P", y)));
        assertNotEquals(mkForall(x.of(Bool), mkApp("P", x)), mkForall(x.of(A), mkApp("P", x)));
    }
    
    @Test
    public void Exists() {
        List<AnnotatedVar> xList = new ArrayList<>();
        xList.add(x.of(A));
        assertEquals(mkExists(x.of(A), mkApp("P", x)), mkExists(xList, mkApp("P", x)));
        assertNotEquals(mkExists(x.of(A), mkApp("P", x)), mkExists(y.of(A), mkApp("P", x)));
        assertNotEquals(mkExists(x.of(A), mkApp("P", x)), mkExists(x.of(A), mkApp("Q", x)));
        assertNotEquals(mkExists(x.of(A), mkApp("P", x)), mkExists(y.of(A), mkApp("P", y)));
        assertNotEquals(mkExists(x.of(Bool), mkApp("P", x)), mkExists(x.of(A), mkApp("P", x)));
    }
    
    @Test
    public void Distinct() {
        List<Term> termList = new ArrayList<>();
        termList.add(x);
        termList.add(y);
        assertEquals(mkDistinct(x, y), mkDistinct(termList));
        assertNotEquals(mkDistinct(x, y), mkDistinct(x, z));
    }
}
