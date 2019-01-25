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
    Var a1 = mkVar("a1", A);
    Var a2 = mkVar("a2", A);
    Var a3 = mkVar("a3", A);
    Var x = mkVar("x", A);
    Var y = mkVar("y", A);
    Var z = mkVar("z", A);
    
    Term p = mkVar("p", Bool);
    Term q = mkVar("q", Bool);
    Term r = mkVar("r", Bool);
    
    FuncDecl P = mkFuncDecl("P", A, Bool);
    FuncDecl Q = mkFuncDecl("Q", A, Bool);
    
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
    public void Iff() {
        assertEquals(mkIff(p, q), mkIff(p, q));
        assertNotEquals(mkIff(p, q), mkIff(p, r));
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
        assertEquals(mkApp(P, a1), mkApp(P, a1List));
        assertNotEquals(mkApp(P, a1), mkApp(P, a2));
        assertNotEquals(mkApp(P, a1), mkApp(Q, a1));
    }
    
    @Test
    public void Forall() {
        List<Var> xList = new ArrayList<>();
        xList.add(x);
        assertEquals(mkForall(x, mkApp(P, x)), mkForall(xList, mkApp(P, x)));
        assertNotEquals(mkForall(x, mkApp(P, x)), mkForall(y, mkApp(P, x)));
        assertNotEquals(mkForall(x, mkApp(P, x)), mkForall(x, mkApp(Q, x)));
        assertNotEquals(mkForall(x, mkApp(P, x)), mkForall(y, mkApp(P, y)));
    }
    
    @Test
    public void Exists() {
        List<Var> xList = new ArrayList<>();
        xList.add(x);
        assertEquals(mkExists(x, mkApp(P, x)), mkExists(xList, mkApp(P, x)));
        assertNotEquals(mkExists(x, mkApp(P, x)), mkExists(y, mkApp(P, x)));
        assertNotEquals(mkExists(x, mkApp(P, x)), mkExists(x, mkApp(Q, x)));
        assertNotEquals(mkExists(x, mkApp(P, x)), mkExists(y, mkApp(P, y)));
    }
    
    @Test
    public void Distinct() {
        List<Var> varList = new ArrayList<>();
        varList.add(x);
        varList.add(y);
        assertEquals(mkDistinct(x, y), mkDistinct(varList));
        assertNotEquals(mkDistinct(x, y), mkDistinct(x, z));
    }
}
