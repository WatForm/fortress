import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;

public class TypeCheckTest {
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Type.Bool);
    FuncDecl Q = FuncDecl.mkFuncDecl("Q", B, Type.Bool);
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, B);
    FuncDecl g = FuncDecl.mkFuncDecl("g", B, A);
    FuncDecl h = FuncDecl.mkFuncDecl("h", Type.Bool, Type.Bool);
    
    @Test(expected = fortress.data.TypeCheckException.UnknownType.class)
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
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void functionAppConstWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g);
        Term app = Term.mkApp("g", x);
        app.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.UnknownFunction.class)
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
            .withFunctionDeclarations(P);
        Term app1 = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term app2 = Term.mkExists(x.of(A), Term.mkApp("P", x));
        
        assertEquals(Type.Bool, app1.typeCheck(sig).type);
        assertEquals(Type.Bool, app2.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void predicateAppForallVarWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants()
            .withFunctionDeclarations(P);
        Term app = Term.mkForall(y.of(B), Term.mkApp("P", y));
        app.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void predicateAppExistsVarWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants()
            .withFunctionDeclarations(P);
        Term app = Term.mkExists(y.of(B), Term.mkApp("P", y));
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
            .withFunctionDeclarations(g, f, P);
        Term fx = Term.mkApp("f", x);
        Term gfx = Term.mkApp("g", fx);
        Term pgfx = Term.mkApp("P", gfx);
        assertEquals(B, fx.typeCheck(sig).type);
        assertEquals(A, gfx.typeCheck(sig).type);
        assertEquals(Type.Bool, pgfx.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void nestedAppWrongArg1() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g, f, P);
        Term fx = Term.mkApp("f", x);
        Term ffx = Term.mkApp("f", fx);
        assertEquals(B, fx.typeCheck(sig).type);
        ffx.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void nestedAppWrongArg2() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g, f, P);
        Term fx = Term.mkApp("f", x);
        Term ffx = Term.mkApp("f", fx);
        Term pffx = Term.mkApp("P", ffx);
        assertEquals(B, fx.typeCheck(sig).type);
        pffx.typeCheck(sig);
    }
    
    @Test
    public void andOrImp() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(y.of(Type.Bool))
            .withFunctionDeclarations(P);
        Term arg1 = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        Term or = Term.mkOr(arg1, arg2);
        Term imp = Term.mkImp(arg1, arg2);
        assertEquals(Type.Bool, and.typeCheck(sig).type);
        assertEquals(Type.Bool, or.typeCheck(sig).type);
        assertEquals(Type.Bool, imp.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
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
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
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
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
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
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
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
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
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
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
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
            .withFunctionDeclarations(P);
        Term not = Term.mkNot(Term.mkApp("P", x));
        assertEquals(Type.Bool, not.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
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
            .withFunctionDeclarations(P, Q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("Q", y));
        assertEquals(Type.Bool, forall.typeCheck(sig).type);
        assertEquals(Type.Bool, exists.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
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
            .withFunctionDeclarations(P, Q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("P", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("Q", y));
        assertEquals(Type.Bool, forall.typeCheck(sig).type);
        assertEquals(Type.Bool, exists.typeCheck(sig).type);
    }
    
    @Test(expected = fortress.data.TypeCheckException.UnknownType.class)
    public void unbound() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants()
            .withFunctionDeclarations(P, Q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("Q", y));
        forall.typeCheck(sig);
    }
    
    // Check that errors percolate upwards
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void nestedError1() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f);
        Term bad1 = Term.mkOr(x, Term.mkTop());
        Term t1 = Term.mkAnd(Term.mkImp(Term.mkNot(bad1), Term.mkBottom()), Term.mkTop());
        t1.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
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
    @Test(expected = fortress.data.TypeCheckException.UnknownType.class)
    public void halfQuantified() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(P);
        
        // x is a free variable in the second and argument -- should fail typechecking
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("P", x)),
            Term.mkApp("P", x)
        );
        
        t.typeCheck(sig);
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
        
        assertEquals(Type.Bool, t.typeCheck(sig).type);
    }
    
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.UnknownType.class)
    public void halfQuantifiedMultiple() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(P);
        
        // x is a free variable in the second and argument -- should fail typechecking
        Term t = Term.mkAnd(
            Term.mkForall(List.of(x.of(A), y.of(A)), Term.mkApp("P", x)),
            Term.mkApp("P", x)
        );
        
        t.typeCheck(sig);
    }
    
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.UnknownType.class)
    public void nonExistentTypeQuantifier() {
        Signature sig = Signature.empty();
        Term t = Term.mkForall(x.of(A), Term.mkTop());
        t.typeCheck(sig);
    }
    
    // Naming tests
    
    // TODO need more tests of this style
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.NameConflict.class)
    public void clashingVarFunction() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(P);
        Var xp = Term.mkVar("P"); // name clashes with function name
        Term t = Term.mkForall(xp.of(Type.Bool), xp);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.NameConflict.class)
    public void clashingVarType() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(P);
        Var xp = Term.mkVar("A"); // name clashes with type name
        Term t = Term.mkForall(xp.of(Type.Bool), xp);
        t.typeCheck(sig);
    }
    
    // Term structure
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void forallInsideApp() {
        // Forall is not allowed inside an application
        Signature sig = Signature.empty()
            .withTypes(A)
            .withFunctionDeclarations(h);
        Term t = Term.mkApp("h", Term.mkForall(x.of(A), Term.mkTop()));
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void existsInsideApp() {
        // Exists is not allowed inside an application
        Signature sig = Signature.empty()
            .withTypes(A)
            .withFunctionDeclarations(h);
        Term t = Term.mkApp("h", Term.mkExists(x.of(A), Term.mkTop()));
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void connectiveInsideApp() {
        // Logical connectives are not allowed inside an application
        Signature sig = Signature.empty()
            .withFunctionDeclaration(h);
        Term t = Term.mkApp("h", Term.mkAnd(Term.mkTop(), Term.mkTop()));
        t.typeCheck(sig);
            
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void negationInsideApp() {
        // Negation is not allowed inside an application
        Signature sig = Signature.empty()
            .withFunctionDeclaration(h);
        Term t = Term.mkApp("h", Term.mkNot(Term.mkTop()));
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void equalsInsideApp() {
        // = is not allowed inside an application
        Signature sig = Signature.empty()
            .withType(A)
            .withConstant(x.of(A))
            .withFunctionDeclaration(h);
        Term t = Term.mkApp("h", Term.mkEq(x, x));
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void distinctInsideApp() {
        // distinct is not allowed inside an application
        Signature sig = Signature.empty()
            .withType(A)
            .withConstant(x.of(A))
            .withFunctionDeclaration(h);
        Term t = Term.mkApp("h", Term.mkDistinct(x, x));
        t.typeCheck(sig);
    }
}
