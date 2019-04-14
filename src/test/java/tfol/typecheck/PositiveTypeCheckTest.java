import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;

public class PositiveTypeCheckTest {
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Type.Bool());
    FuncDecl Q = FuncDecl.mkFuncDecl("Q", B, Type.Bool());
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, B);
    FuncDecl g = FuncDecl.mkFuncDecl("g", B, A);
    FuncDecl h = FuncDecl.mkFuncDecl("h", Type.Bool(), Type.Bool());
    FuncDecl R = FuncDecl.mkFuncDecl("R", A, A, Type.Bool());
    FuncDecl next = FuncDecl.mkFuncDecl("next", A, A);
    
    @Test
    public void constant() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations();
        
        assertEquals(A, x.typeCheck(sig).type);
    }
    
    @Test
    public void functionAppConst() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(f);
        Term app = Term.mkApp("f", x);
        
        assertEquals(B, app.typeCheck(sig).type);
    }
    
    @Test
    public void predicateAppQuantifiedVar() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(P);
        Term app1 = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term app2 = Term.mkExists(x.of(A), Term.mkApp("P", x));
        
        assertEquals(Type.Bool(), app1.typeCheck(sig).type);
        assertEquals(Type.Bool(), app2.typeCheck(sig).type);
    }
    
    @Test
    public void quantifiedBoolAnd() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(h);
        Term term1 = Term.mkForall(x.of(Type.Bool()), Term.mkOr(x, Term.mkApp("h", x)));
        Term term2 = Term.mkForall(x.of(Type.Bool()), Term.mkOr(x, Term.mkApp("h", x)));
        
        assertEquals(Type.Bool(), term1.typeCheck(sig).type);
        assertEquals(Type.Bool(), term2.typeCheck(sig).type);
    }
    
    @Test
    public void nestedApp() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g, f, P);
        Term fx = Term.mkApp("f", x);
        Term gfx = Term.mkApp("g", fx);
        Term pgfx = Term.mkApp("P", gfx);
        assertEquals(B, fx.typeCheck(sig).type);
        assertEquals(A, gfx.typeCheck(sig).type);
        assertEquals(Type.Bool(), pgfx.typeCheck(sig).type);
    }
    
    @Test
    public void andOrImp() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(y.of(Type.Bool()))
            .withFunctionDeclarations(P);
        Term arg1 = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        Term or = Term.mkOr(arg1, arg2);
        Term imp = Term.mkImp(arg1, arg2);
        assertEquals(Type.Bool(), and.typeCheck(sig).type);
        assertEquals(Type.Bool(), or.typeCheck(sig).type);
        assertEquals(Type.Bool(), imp.typeCheck(sig).type);
    }
    
    
    @Test
    public void eqDistinct() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("f", Term.mkApp("g", Term.mkApp("f", x)));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        Term eq1 = Term.mkEq(arg1, arg2);
        Term eq2 = Term.mkEq(arg1, arg3);
        Term eq3 = Term.mkEq(arg2, arg3);
        assertEquals(Type.Bool(), distinct.typeCheck(sig).type);
        assertEquals(Type.Bool(), eq1.typeCheck(sig).type);
        assertEquals(Type.Bool(), eq2.typeCheck(sig).type);
        assertEquals(Type.Bool(), eq3.typeCheck(sig).type);
    }
    
    @Test
    public void topBottom() {
        Signature sig = Signature.empty()
            .withTypes()
            .withConstants()
            .withFunctionDeclarations();
        assertEquals(Type.Bool(), Term.mkTop().typeCheck(sig).type);
        assertEquals(Type.Bool(), Term.mkBottom().typeCheck(sig).type);
        
    }
    
    @Test
    public void not() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations(P);
        Term not = Term.mkNot(Term.mkApp("P", x));
        assertEquals(Type.Bool(), not.typeCheck(sig).type);
    }
    
    @Test
    public void quantifier() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants()
            .withFunctionDeclarations(P, Q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("Q", y));
        assertEquals(Type.Bool(), forall.typeCheck(sig).type);
        assertEquals(Type.Bool(), exists.typeCheck(sig).type);
    }
    
    @Test
    public void quantifierShadow() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(B), y.of(A))
            .withFunctionDeclarations(P, Q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("Q", y));
        assertEquals(Type.Bool(), forall.typeCheck(sig).type);
        assertEquals(Type.Bool(), exists.typeCheck(sig).type);
    }
    
    @Test
    public void halfQuantifiedButConstant() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations(P);
        
        // x is free in the second and argument -- but it is a constant so this is fine
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("P", x)),
            Term.mkApp("P", x)
        );
        
        assertEquals(Type.Bool(), t.typeCheck(sig).type);
    }

    @Test
    public void transitiveClosure() {
        Signature sig = Signature.empty()
            .withType(A)
            .withFunctionDeclaration(R)
            .withConstants(x.of(A), y.of(A));
        Term t = Term.mkTC("R", x, y);
        
        assertEquals(Type.Bool(), t.typeCheck(sig).type);
    }
    
    @Test
    public void transitiveClosureFunction() {
        Signature sig = Signature.empty()
            .withType(A)
            .withFunctionDeclaration(next)
            .withConstants(x.of(A), y.of(A), z.of(A));
        Term t = Term.mkTC("next", x, y);
        
        assertEquals(Type.Bool(), t.typeCheck(sig).type);
    }
    
    @Test
    public void domainElement() {
        Signature sig = Signature.empty()
            .withType(A);
        
        Term t = Term.mkDomainElement(2, A);
        
        assertEquals(A, t.typeCheck(sig).type);
    }
    
}