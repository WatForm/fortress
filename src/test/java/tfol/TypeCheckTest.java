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
        Signature sig = Signature.mkSignature(types, decls, constants);
        assertEquals(Optional.empty(), x.typecheckOption(sig));
    }
    
    @Test
    public void constant() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of();
        Signature sig = Signature.mkSignature(types, decls, constants);
        assertEquals(Optional.of(A), x.typecheckOption(sig));
    }
    
    @Test
    public void functionAppConst() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(f);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term app = Term.mkApp("f", x);
        assertEquals(Optional.of(B), app.typecheckOption(sig));
    }
    
    @Test
    public void functionAppConstWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(f);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term app = Term.mkApp("g", x);
        assertEquals(Optional.empty(), app.typecheckOption(sig));
    }
    
    @Test
    public void functionAppConstMissingDecl() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of();
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term app = Term.mkApp("f", x);
        assertEquals(Optional.empty(), app.typecheckOption(sig));
    }
    
    @Test
    public void predicateAppQuantifiedVar() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term app1 = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term app2 = Term.mkExists(x.of(A), Term.mkApp("p", x));
        assertEquals(Optional.of(Type.Bool), app1.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), app2.typecheckOption(sig));
    }
    
    @Test
    public void predicateAppQuantifiedVarWrongArg() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term app1 = Term.mkForall(y.of(B), Term.mkApp("p", y));
        Term app2 = Term.mkExists(y.of(B), Term.mkApp("p", y));
        assertEquals(Optional.empty(), app1.typecheckOption(sig));
        assertEquals(Optional.empty(), app2.typecheckOption(sig));
    }
    
    @Test
    public void quantifiedBoolAnd() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(h);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term term1 = Term.mkForall(x.of(Type.Bool), Term.mkOr(x, Term.mkApp("h", x)));
        Term term2 = Term.mkForall(x.of(Type.Bool), Term.mkOr(x, Term.mkApp("h", x)));
        assertEquals(Optional.of(Type.Bool), term1.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), term2.typecheckOption(sig));
    }
    
    @Test
    public void nestedApp() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(g, f, p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term fx = Term.mkApp("f", x);
        Term gfx = Term.mkApp("g", fx);
        Term pgfx = Term.mkApp("p", gfx);
        assertEquals(Optional.of(B), fx.typecheckOption(sig));
        assertEquals(Optional.of(A), gfx.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), pgfx.typecheckOption(sig));
    }
    
    @Test
    public void nestedAppWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(g, f, p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term fx = Term.mkApp("f", x);
        Term ffx = Term.mkApp("f", fx);
        Term pffx = Term.mkApp("p", ffx);
        assertEquals(Optional.of(B), fx.typecheckOption(sig));
        assertEquals(Optional.empty(), ffx.typecheckOption(sig));
        assertEquals(Optional.empty(), pffx.typecheckOption(sig));
    }
    
    @Test
    public void andOrImp() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(y.of(Type.Bool));
        Set<FuncDecl> decls = Set.of(p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term arg1 = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        Term or = Term.mkOr(arg1, arg2);
        Term imp = Term.mkImp(arg1, arg2);
        assertEquals(Optional.of(Type.Bool), and.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), or.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), imp.typecheckOption(sig));
    }
    
    @Test
    public void andOrImpWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A), y.of(Type.Bool));
        Set<FuncDecl> decls = Set.of(f);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        Term or = Term.mkOr(arg1, arg2);
        Term imp = Term.mkImp(arg1, arg2);
        assertEquals(Optional.empty(), and.typecheckOption(sig));
        assertEquals(Optional.empty(), or.typecheckOption(sig));
        assertEquals(Optional.empty(), imp.typecheckOption(sig));
    }
    
    @Test
    public void eqDistinct() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A), y.of(B));
        Set<FuncDecl> decls = Set.of(f, g);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("f", Term.mkApp("g", Term.mkApp("f", x)));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        Term eq1 = Term.mkEq(arg1, arg2);
        Term eq2 = Term.mkEq(arg1, arg3);
        Term eq3 = Term.mkEq(arg2, arg3);
        assertEquals(Optional.of(Type.Bool), distinct.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), eq1.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), eq2.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), eq3.typecheckOption(sig));
    }
    
    @Test
    public void eqDistinctWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A), y.of(B));
        Set<FuncDecl> decls = Set.of(f, g);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("g", Term.mkApp("f", x));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        Term eq1 = Term.mkEq(arg1, arg3);
        Term eq2 = Term.mkEq(arg2, arg3);
        assertEquals(Optional.empty(), distinct.typecheckOption(sig));
        assertEquals(Optional.empty(), eq1.typecheckOption(sig));
        assertEquals(Optional.empty(), eq2.typecheckOption(sig));
    }
    
    @Test
    public void topBottom() {
        Set<Type> types = Set.of();
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of();
        Signature sig = Signature.mkSignature(types, decls, constants);
        assertEquals(Optional.of(Type.Bool), Term.mkTop().typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), Term.mkBottom().typecheckOption(sig));
        
    }
    
    @Test
    public void not() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term not = Term.mkNot(Term.mkApp("p", x));
        assertEquals(Optional.of(Type.Bool), not.typecheckOption(sig));
    }
    
    @Test
    public void notWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(f);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term not = Term.mkNot(Term.mkApp("f", x));
        assertEquals(Optional.empty(), not.typecheckOption(sig));
    }
    
    @Test
    public void quantifier() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p, q);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("q", y));
        assertEquals(Optional.of(Type.Bool), forall.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), exists.typecheckOption(sig));
    }
    
    @Test
    public void quantifierWrongArg() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(f, g);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("f", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("g", y));
        assertEquals(Optional.empty(), forall.typecheckOption(sig));
        assertEquals(Optional.empty(), exists.typecheckOption(sig));
    }
    
    @Test
    public void quantifierShadow() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(B), y.of(A));
        Set<FuncDecl> decls = Set.of(p, q);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term exists = Term.mkExists(y.of(B), Term.mkApp("q", y));
        assertEquals(Optional.of(Type.Bool), forall.typecheckOption(sig));
        assertEquals(Optional.of(Type.Bool), exists.typecheckOption(sig));
    }
    
    @Test
    public void unbound() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p, q);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("q", y));
        Term exists = Term.mkExists(x.of(A), Term.mkApp("q", y));
        assertEquals(Optional.empty(), forall.typecheckOption(sig));
        assertEquals(Optional.empty(), exists.typecheckOption(sig));
    }
    
    // Check that errors percolate upwards
    @Test
    public void nestedError() {
        Set<Type> types = Set.of(A, B);
        Set<AnnotatedVar> constants = Set.of(x.of(A), y.of(B));
        Set<FuncDecl> decls = Set.of(f);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Term bad1 = Term.mkOr(x, Term.mkTop());
        Term bad2 = Term.mkApp("f", y);
        Term t1 = Term.mkAnd(Term.mkImp(Term.mkNot(bad1), Term.mkBottom()), Term.mkTop());
        Term t2 = Term.mkOr(Term.mkEq(y, bad2), Term.mkTop());
        assertEquals(Optional.empty(), t1.typecheckOption(sig));
        assertEquals(Optional.empty(), t2.typecheckOption(sig));
    }
    
    @Test // Former bug
    public void halfQuantified() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        
        // x is a free variable in the second and argument -- should fail typechecking
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("p", x)),
            Term.mkApp("p", x)
        );
        
        assertEquals(Optional.empty(), t.typecheckOption(sig));
    }
    
    @Test
    public void halfQuantifiedButConstant() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of(x.of(A));
        Set<FuncDecl> decls = Set.of(p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        
        // x is free in the second and argument -- but it is a constant so this is fine
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("p", x)),
            Term.mkApp("p", x)
        );
        
        assertEquals(Optional.of(Type.Bool), t.typecheckOption(sig));
    }
    
    @Test // Former bug
    public void halfQuantifiedMultiple() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        
        // x is a free variable in the second and argument -- should fail typechecking
        Term t = Term.mkAnd(
            Term.mkForall(List.of(x.of(A), y.of(A)), Term.mkApp("p", x)),
            Term.mkApp("p", x)
        );
        
        assertEquals(Optional.empty(), t.typecheckOption(sig));
    }
    
    
    // TODO need more tests of this style
    @Test // Former bug
    public void badName() {
        Set<Type> types = Set.of(A);
        Set<AnnotatedVar> constants = Set.of();
        Set<FuncDecl> decls = Set.of(p);
        Signature sig = Signature.mkSignature(types, decls, constants);
        Var xp = Term.mkVar("p"); // name clashes with function name
        Term t = Term.mkForall(xp.of(Type.Bool), xp);
        assertEquals(Optional.empty(), t.typecheckOption(sig));
    }
}
