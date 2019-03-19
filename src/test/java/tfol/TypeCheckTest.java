import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.tfol.Term.*;
import fortress.tfol.Type.*;
import fortress.tfol.FuncDecl.*;
import fortress.tfol.*;
import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;
import java.util.Optional;

public class TypeCheckTest {
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    FuncDecl p = FuncDecl.mkFuncDecl("p", A, Type.Bool);
    FuncDecl q = FuncDecl.mkFuncDecl("q", B, Type.Bool);
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, B);
    FuncDecl g = FuncDecl.mkFuncDecl("g", B, A);
    FuncDecl h = FuncDecl.mkFuncDecl("h", Type.Bool, Type.Bool);
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void freeVar() {
        Signature sig = Signature.empty()
            .withType(A)
            .withConstants()
            .withFunctionDeclarations();
        
        x.typeCheck(sig);
    }
    
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
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void functionAppConstWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(f);
        Term app = Term.mkApp("g", x);
        app.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void functionAppConstMissingDecl() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations();
        Term app = Term.mkApp("f", x);
        app.typeCheck(sig);
    }
    
    @Test
    public void predicateAppQuantifiedVar() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(p);
        Term app1 = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term app2 = Term.mkExists(x.of(A), Term.mkApp("p", x));
        
        assertEquals(Type.Bool, app1.typeCheck(sig).type);
        assertEquals(Type.Bool, app2.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void predicateAppForallVarWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(p);
        Term app = Term.mkForall(y.of(B), Term.mkApp("p", y));
        app.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void predicateAppExistsVarWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(p);
        Term app = Term.mkExists(y.of(B), Term.mkApp("p", y));
        app.typeCheck(sig);
    }
    
    @Test
    public void quantifiedBoolAnd() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(h);
        Term term1 = Term.mkForall(x.of(Type.Bool), Term.mkOr(x, Term.mkApp("h", x)));
        Term term2 = Term.mkForall(x.of(Type.Bool), Term.mkOr(x, Term.mkApp("h", x)));
        
        assertEquals(Type.Bool, term1.typeCheck(sig).type);
        assertEquals(Type.Bool, term2.typeCheck(sig).type);
    }
    
    @Test
    public void nestedApp() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g, f, p);
        Term fx = Term.mkApp("f", x);
        Term gfx = Term.mkApp("g", fx);
        Term pgfx = Term.mkApp("p", gfx);
        assertEquals(B, fx.typeCheck(sig).type);
        assertEquals(A, gfx.typeCheck(sig).type);
        assertEquals(Type.Bool, pgfx.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void nestedAppWrongArg1() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g, f, p);
        Term fx = Term.mkApp("f", x);
        Term ffx = Term.mkApp("f", fx);
        assertEquals(B, fx.typeCheck(sig).type);
        ffx.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void nestedAppWrongArg2() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g, f, p);
        Term fx = Term.mkApp("f", x);
        Term ffx = Term.mkApp("f", fx);
        Term pffx = Term.mkApp("p", ffx);
        assertEquals(B, fx.typeCheck(sig).type);
        pffx.typeCheck(sig);
    }
    
    @Test
    public void andOrImp() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(y.of(Type.Bool))
            .withFunctionDeclarations(p);
        Term arg1 = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        Term or = Term.mkOr(arg1, arg2);
        Term imp = Term.mkImp(arg1, arg2);
        assertEquals(Type.Bool, and.typeCheck(sig).type);
        assertEquals(Type.Bool, or.typeCheck(sig).type);
        assertEquals(Type.Bool, imp.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void andWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(Type.Bool))
            .withFunctionDeclarations(f);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        and.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void orWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(Type.Bool))
            .withFunctionDeclarations(f);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term or = Term.mkOr(arg1, arg2);
        or.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void impWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(Type.Bool))
            .withFunctionDeclarations(f);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term imp = Term.mkImp(arg1, arg2);
        imp.typeCheck(sig);
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
        assertEquals(Type.Bool, distinct.typeCheck(sig).type);
        assertEquals(Type.Bool, eq1.typeCheck(sig).type);
        assertEquals(Type.Bool, eq2.typeCheck(sig).type);
        assertEquals(Type.Bool, eq3.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void distinctWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("g", Term.mkApp("f", x));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        distinct.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void eqWrongArg1() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("g", Term.mkApp("f", x));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        Term eq1 = Term.mkEq(arg1, arg3);
        eq1.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void eqWrongArg2() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("g", Term.mkApp("f", x));
        Term eq2 = Term.mkEq(arg2, arg3);
        eq2.typeCheck(sig);
    }
    
    @Test
    public void topBottom() {
        Signature sig = Signature.empty()
            .withTypes()
            .withConstants()
            .withFunctionDeclarations();
        assertEquals(Type.Bool, Term.mkTop().typeCheck(sig).type);
        assertEquals(Type.Bool, Term.mkBottom().typeCheck(sig).type);
        
    }
    
    @Test
    public void not() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations(p);
        Term not = Term.mkNot(Term.mkApp("p", x));
        assertEquals(Type.Bool, not.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void notWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(f);
        Term not = Term.mkNot(Term.mkApp("f", x));
        not.typeCheck(sig);
    }
    
    @Test
    public void quantifier() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants()
            .withFunctionDeclarations(p, q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("q", y));
        assertEquals(Type.Bool, forall.typeCheck(sig).type);
        assertEquals(Type.Bool, exists.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void forallWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants()
            .withFunctionDeclarations(f, g);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("f", x));
        forall.typeCheck(sig);
    }
    
    @Test
    public void quantifierShadow() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(B), y.of(A))
            .withFunctionDeclarations(p, q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("q", y));
        assertEquals(Type.Bool, forall.typeCheck(sig).type);
        assertEquals(Type.Bool, exists.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void unbound() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants()
            .withFunctionDeclarations(p, q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("q", y));
        forall.typeCheck(sig);
    }
    
    // Check that errors percolate upwards
    @Test(expected = fortress.data.TypeCheckException.class)
    public void nestedError1() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f);
        Term bad1 = Term.mkOr(x, Term.mkTop());
        Term t1 = Term.mkAnd(Term.mkImp(Term.mkNot(bad1), Term.mkBottom()), Term.mkTop());
        t1.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void nestedError2() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f);
        Term bad2 = Term.mkApp("f", y);
        Term t2 = Term.mkOr(Term.mkEq(y, bad2), Term.mkTop());
        t2.typeCheck(sig);
    }
    
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.class)
    public void halfQuantified() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(p);
        
        // x is a free variable in the second and argument -- should fail typechecking
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("p", x)),
            Term.mkApp("p", x)
        );
        
        t.typeCheck(sig);
    }
    
    @Test
    public void halfQuantifiedButConstant() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations(p);
        
        // x is free in the second and argument -- but it is a constant so this is fine
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("p", x)),
            Term.mkApp("p", x)
        );
        
        assertEquals(Type.Bool, t.typeCheck(sig).type);
    }
    
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.class)
    public void halfQuantifiedMultiple() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(p);
        
        // x is a free variable in the second and argument -- should fail typechecking
        Term t = Term.mkAnd(
            Term.mkForall(List.of(x.of(A), y.of(A)), Term.mkApp("p", x)),
            Term.mkApp("p", x)
        );
        
        t.typeCheck(sig);
    }
    
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.class)
    public void nonExistentTypeQuantifier() {
        Signature sig = Signature.empty();
        Term t = Term.mkForall(x.of(A), Term.mkTop());
        t.typeCheck(sig);
    }
    
    // Naming tests
    
    // TODO need more tests of this style
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.class)
    public void clashingVarFunction() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(p);
        Var xp = Term.mkVar("p"); // name clashes with function name
        Term t = Term.mkForall(xp.of(Type.Bool), xp);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.class)
    public void clashingVarType() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(p);
        Var xp = Term.mkVar("A"); // name clashes with type name
        Term t = Term.mkForall(xp.of(Type.Bool), xp);
        t.typeCheck(sig);
    }
    
    // Term structure
    
    // Sanitization
}
