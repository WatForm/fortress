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
    
    // TODO need more descriptive typecheck error messages
    // so can check failing for the expected reasons
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    FuncDecl p = FuncDecl.mkFuncDecl("p", A, Type.Bool);
    FuncDecl q = FuncDecl.mkFuncDecl("q", B, Type.Bool);
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, B);
    FuncDecl g = FuncDecl.mkFuncDecl("g", B, A);
    FuncDecl h = FuncDecl.mkFuncDecl("h", Type.Bool, Type.Bool);
    
    @Test
    public void freeVar() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of();
        assertEquals(Optional.empty(), Term.typeCheck(x, types, constants, decls));
    }
    
    @Test
    public void constant() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of();
        assertEquals(Optional.of(A), Term.typeCheck(x, types, constants, decls));
    }
    
    @Test
    public void functionAppConst() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(f);
        Term app = Term.mkApp("f", x);
        assertEquals(Optional.of(B), Term.typeCheck(app, types, constants, decls));
    }
    
    @Test
    public void functionAppConstWrongArg() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(f);
        Term app = Term.mkApp("g", x);
        assertEquals(Optional.empty(), Term.typeCheck(app, types, constants, decls));
    }
    
    @Test
    public void functionAppConstMissingDecl() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of();
        Term app = Term.mkApp("f", x);
        assertEquals(Optional.empty(), Term.typeCheck(app, types, constants, decls));
    }
    
    @Test
    public void predicateAppQuantifiedVar() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        Term app1 = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term app2 = Term.mkExists(x.of(A), Term.mkApp("p", x));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(app1, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(app2, types, constants, decls));
    }
    
    @Test
    public void predicateAppQuantifiedVarWrongArg() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        Term app1 = Term.mkForall(y.of(B), Term.mkApp("p", y));
        Term app2 = Term.mkExists(y.of(B), Term.mkApp("p", y));
        assertEquals(Optional.empty(), Term.typeCheck(app1, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(app2, types, constants, decls));
    }
    
    @Test
    public void quantifiedBoolAnd() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(h);
        Term term1 = Term.mkForall(x.of(Type.Bool), Term.mkOr(x, Term.mkApp("h", x)));
        Term term2 = Term.mkForall(x.of(Type.Bool), Term.mkOr(x, Term.mkApp("h", x)));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(term1, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(term2, types, constants, decls));
    }
    
    @Test
    public void nestedApp() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(g, f, p);
        Term fx = Term.mkApp("f", x);
        Term gfx = Term.mkApp("g", fx);
        Term pgfx = Term.mkApp("p", gfx);
        assertEquals(Optional.of(B), Term.typeCheck(fx, types, constants, decls));
        assertEquals(Optional.of(A), Term.typeCheck(gfx, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(pgfx, types, constants, decls));
    }
    
    @Test
    public void nestedAppWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(g, f, p);
        Term fx = Term.mkApp("f", x);
        Term ffx = Term.mkApp("f", fx);
        Term pffx = Term.mkApp("p", ffx);
        assertEquals(Optional.of(B), Term.typeCheck(fx, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(ffx, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(pffx, types, constants, decls));
    }
    
    @Test
    public void andOrImpIff() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(y.of(Type.Bool));
        Set<FuncDecl> decls = Set.of(p);
        Term arg1 = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        Term or = Term.mkOr(arg1, arg2);
        Term imp = Term.mkImp(arg1, arg2);
        Term iff = Term.mkIff(arg1, arg2);
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(and, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(or, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(imp, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(iff, types, constants, decls));
    }
    
    @Test
    public void andOrImpIffWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A), y.of(Type.Bool));
        Set<FuncDecl> decls = Set.of(f);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        Term or = Term.mkOr(arg1, arg2);
        Term imp = Term.mkImp(arg1, arg2);
        Term iff = Term.mkIff(arg1, arg2);
        assertEquals(Optional.empty(), Term.typeCheck(and, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(or, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(imp, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(iff, types, constants, decls));
    }
    
    @Test
    public void eqDistinct() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A), y.of(B));
        Set<FuncDecl> decls = Set.of(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("f", Term.mkApp("g", Term.mkApp("f", x)));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        Term eq1 = Term.mkEq(arg1, arg2);
        Term eq2 = Term.mkEq(arg1, arg3);
        Term eq3 = Term.mkEq(arg2, arg3);
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(distinct, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(eq1, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(eq2, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(eq3, types, constants, decls));
    }
    
    @Test
    public void eqDistinctWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A), y.of(B));
        Set<FuncDecl> decls = Set.of(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("g", Term.mkApp("f", x));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        Term eq1 = Term.mkEq(arg1, arg3);
        Term eq2 = Term.mkEq(arg2, arg3);
        assertEquals(Optional.empty(), Term.typeCheck(distinct, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(eq1, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(eq2, types, constants, decls));
    }
    
    @Test
    public void topBottom() {
        Set<Type> types = Set.of();
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of();
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(Term.mkTop(), types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(Term.mkBottom(), types, constants, decls));
        
    }
    
    @Test
    public void not() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(p);
        Term not = Term.mkNot(Term.mkApp("p", x));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(not, types, constants, decls));
    }
    
    @Test
    public void notWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(f);
        Term not = Term.mkNot(Term.mkApp("f", x));
        assertEquals(Optional.empty(), Term.typeCheck(not, types, constants, decls));
    }
    
    @Test
    public void quantifier() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p, q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("q", y));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(forall, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(exists, types, constants, decls));
    }
    
    @Test
    public void quantifierWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(f, g);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("f", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("g", y));
        assertEquals(Optional.empty(), Term.typeCheck(forall, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(exists, types, constants, decls));
    }
    
    @Test
    public void quantifierShadow() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(B), y.of(A));
        Set<FuncDecl> decls = Set.of(p, q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("q", y));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(forall, types, constants, decls));
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(exists, types, constants, decls));
    }
    
    @Test
    public void unbound() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p, q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("q", y));
        Term exists = Term.mkExists(x.of(A), Term.mkApp("q", y));
        assertEquals(Optional.empty(), Term.typeCheck(forall, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(exists, types, constants, decls));
    }
    
    // Check that errors percolate upwards
    @Test
    public void nestedError() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A), y.of(B));
        Set<FuncDecl> decls = Set.of(f);
        Term bad1 = Term.mkOr(x, Term.mkTop());
        Term bad2 = Term.mkApp("f", y);
        Term t1 = Term.mkAnd(Term.mkImp(Term.mkNot(bad1), Term.mkBottom()), Term.mkTop());
        Term t2 = Term.mkOr(Term.mkEq(y, bad2), Term.mkTop());
        assertEquals(Optional.empty(), Term.typeCheck(t1, types, constants, decls));
        assertEquals(Optional.empty(), Term.typeCheck(t2, types, constants, decls));
    }
    
    @Test // Former bug
    public void halfQuantified() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        
        // x is a free variable in the second and argument -- should fail typechecking
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("p", x)),
            Term.mkApp("p", x)
        );
        
        assertEquals(Optional.empty(), Term.typeCheck(t, types, constants, decls));
    }
    
    @Test
    public void halfQuantifiedButConstant() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(p);
        
        // x is free in the second and argument -- but it is a constant so this is fine
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("p", x)),
            Term.mkApp("p", x)
        );
        
        assertEquals(Optional.of(Type.Bool), Term.typeCheck(t, types, constants, decls));
    }
    
    @Test // TODO bug
    public void halfQuantifiedMultiple() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        
        // x is a free variable in the second and argument -- should fail typechecking
        Term t = Term.mkAnd(
            Term.mkForall(List.of(x.of(A), y.of(A)), Term.mkApp("p", x)),
            Term.mkApp("p", x)
        );
        
        assertEquals(Optional.empty(), Term.typeCheck(t, types, constants, decls));
    }
    
    
    // TODO need more tests of this style
    @Test
    public void badName() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        Var xp = Term.mkVar("p"); // name clashes with function name
        Term t = Term.mkForall(xp.of(Type.Bool), xp);
        assertEquals(Optional.empty(), Term.typeCheck(t, types, constants, decls));
    }
}
