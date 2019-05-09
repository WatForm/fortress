import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;

public class PositiveTypeCheckTest {
    
    Sort A = Sort.mkSortConst("A");
    Sort B = Sort.mkSortConst("B");
    
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Sort.Bool());
    FuncDecl Q = FuncDecl.mkFuncDecl("Q", B, Sort.Bool());
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, B);
    FuncDecl g = FuncDecl.mkFuncDecl("g", B, A);
    FuncDecl h = FuncDecl.mkFuncDecl("h", Sort.Bool(), Sort.Bool());
    FuncDecl R = FuncDecl.mkFuncDecl("R", A, A, Sort.Bool());
    FuncDecl next = FuncDecl.mkFuncDecl("next", A, A);
    
    @Test
    public void constant() {
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations();
        
        assertEquals(A, x.typeCheck(sig).sort());
    }
    
    @Test
    public void functionAppConst() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(f);
        Term app = Term.mkApp("f", x);
        
        assertEquals(B, app.typeCheck(sig).sort());
    }
    
    @Test
    public void predicateAppQuantifiedVar() {
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants()
            .withFunctionDeclarations(P);
        Term app1 = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term app2 = Term.mkExists(x.of(A), Term.mkApp("P", x));
        
        assertEquals(Sort.Bool(), app1.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), app2.typeCheck(sig).sort());
    }
    
    @Test
    public void quantifiedBoolAnd() {
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants()
            .withFunctionDeclarations(h);
        Term term1 = Term.mkForall(x.of(Sort.Bool()), Term.mkOr(x, Term.mkApp("h", x)));
        Term term2 = Term.mkForall(x.of(Sort.Bool()), Term.mkOr(x, Term.mkApp("h", x)));
        
        assertEquals(Sort.Bool(), term1.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), term2.typeCheck(sig).sort());
    }
    
    @Test
    public void nestedApp() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g, f, P);
        Term fx = Term.mkApp("f", x);
        Term gfx = Term.mkApp("g", fx);
        Term pgfx = Term.mkApp("P", gfx);
        assertEquals(B, fx.typeCheck(sig).sort());
        assertEquals(A, gfx.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), pgfx.typeCheck(sig).sort());
    }
    
    @Test
    public void andOrImp() {
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants(y.of(Sort.Bool()))
            .withFunctionDeclarations(P);
        Term arg1 = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        Term or = Term.mkOr(arg1, arg2);
        Term imp = Term.mkImp(arg1, arg2);
        assertEquals(Sort.Bool(), and.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), or.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), imp.typeCheck(sig).sort());
    }
    
    
    @Test
    public void eqDistinct() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("f", Term.mkApp("g", Term.mkApp("f", x)));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        Term eq1 = Term.mkEq(arg1, arg2);
        Term eq2 = Term.mkEq(arg1, arg3);
        Term eq3 = Term.mkEq(arg2, arg3);
        assertEquals(Sort.Bool(), distinct.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), eq1.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), eq2.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), eq3.typeCheck(sig).sort());
    }
    
    @Test
    public void topBottom() {
        Signature sig = Signature.empty()
            .withSorts()
            .withConstants()
            .withFunctionDeclarations();
        assertEquals(Sort.Bool(), Term.mkTop().typeCheck(sig).sort());
        assertEquals(Sort.Bool(), Term.mkBottom().typeCheck(sig).sort());
        
    }
    
    @Test
    public void not() {
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations(P);
        Term not = Term.mkNot(Term.mkApp("P", x));
        assertEquals(Sort.Bool(), not.typeCheck(sig).sort());
    }
    
    @Test
    public void quantifier() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants()
            .withFunctionDeclarations(P, Q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("Q", y));
        assertEquals(Sort.Bool(), forall.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), exists.typeCheck(sig).sort());
    }
    
    @Test
    public void quantifierShadow() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(B), y.of(A))
            .withFunctionDeclarations(P, Q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("Q", y));
        assertEquals(Sort.Bool(), forall.typeCheck(sig).sort());
        assertEquals(Sort.Bool(), exists.typeCheck(sig).sort());
    }
    
    @Test
    public void halfQuantifiedButConstant() {
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations(P);
        
        // x is free in the second and argument -- but it is a constant so this is fine
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("P", x)),
            Term.mkApp("P", x)
        );
        
        assertEquals(Sort.Bool(), t.typeCheck(sig).sort());
    }
    
    @Test
    public void domainElement() {
        Signature sig = Signature.empty()
            .withSort(A);
        
        Term t = Term.mkDomainElement(2, A);
        
        assertEquals(A, t.typeCheck(sig).sort());
    }
    
}
