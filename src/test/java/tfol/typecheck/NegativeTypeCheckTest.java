import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.msfol.*;
import java.util.List;

public class NegativeTypeCheckTest {
    
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
    
    FuncDecl transitionRelation = FuncDecl.mkFuncDecl("transition", A, A, Sort.Bool());
    FuncDecl transitionFunction = FuncDecl.mkFuncDecl("transition", A, Sort.Bool());
    
    
    @Test(expected = fortress.data.TypeCheckException.UndeterminedSort.class)
    public void freeVar() {
        // A free var should fail typechecking
        Signature sig = Signature.empty()
            .withSort(A)
            .withConstants()
            .withFunctionDeclarations();
        
        x.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void functionAppConstWrongArg() {
        // Application of a function to a constant of the wrong argument type
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g);
        Term app = Term.mkApp("g", x);
        app.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.UnknownFunction.class)
    public void functionAppConstMissingDecl() {
        // Use of a function that is missing a declaration
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations();
        Term app = Term.mkApp("f", x);
        app.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void predicateAppForallVarWrongArg() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants()
            .withFunctionDeclarations(P);
        Term app = Term.mkForall(y.of(B), Term.mkApp("P", y));
        app.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void predicateAppExistsVarWrongArg() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants()
            .withFunctionDeclarations(P);
        Term app = Term.mkExists(y.of(B), Term.mkApp("P", y));
        app.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void nestedAppWrongArg1() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g, f, P);
        Term fx = Term.mkApp("f", x);
        Term ffx = Term.mkApp("f", fx);
        assertEquals(B, fx.typeCheck(sig).sort());
        ffx.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void nestedAppWrongArg2() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g, f, P);
        Term fx = Term.mkApp("f", x);
        Term ffx = Term.mkApp("f", fx);
        Term pffx = Term.mkApp("P", ffx);
        assertEquals(B, fx.typeCheck(sig).sort());
        pffx.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void andWrongArg() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A), y.of(Sort.Bool()))
            .withFunctionDeclarations(f);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term and = Term.mkAnd(arg1, arg2);
        and.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void orWrongArg() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A), y.of(Sort.Bool()))
            .withFunctionDeclarations(f);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term or = Term.mkOr(arg1, arg2);
        or.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void impWrongArg() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A), y.of(Sort.Bool()))
            .withFunctionDeclarations(f);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term imp = Term.mkImp(arg1, arg2);
        imp.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void distinctWrongArg() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("g", Term.mkApp("f", x));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        distinct.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void eqWrongArg1() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("g", Term.mkApp("f", x));
        Term distinct = Term.mkDistinct(arg1, arg2, arg3);
        Term eq1 = Term.mkEq(arg1, arg3);
        eq1.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void eqWrongArg2() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f, g);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term arg3 = Term.mkApp("g", Term.mkApp("f", x));
        Term eq2 = Term.mkEq(arg2, arg3);
        eq2.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void notWrongArg() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(f);
        Term not = Term.mkNot(Term.mkApp("f", x));
        not.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void forallWrongArg() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants()
            .withFunctionDeclarations(f, g);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("f", x));
        forall.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.UndeterminedSort.class)
    public void unbound() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants()
            .withFunctionDeclarations(P, Q);
        Term forall = Term.mkForall(x.of(A), Term.mkApp("Q", y));
        forall.typeCheck(sig);
    }
    
    // Check that errors percolate upwards
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void nestedError1() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f);
        Term bad1 = Term.mkOr(x, Term.mkTop());
        Term t1 = Term.mkAnd(Term.mkImp(Term.mkNot(bad1), Term.mkBottom()), Term.mkTop());
        t1.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void nestedError2() {
        Signature sig = Signature.empty()
            .withSorts(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclarations(f);
        Term bad2 = Term.mkApp("f", y);
        Term t2 = Term.mkOr(Term.mkEq(y, bad2), Term.mkTop());
        t2.typeCheck(sig);
    }
    
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.UndeterminedSort.class)
    public void halfQuantified() {
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants()
            .withFunctionDeclarations(P);
        
        // x is a free variable in the second and argument -- should fail typechecking
        Term t = Term.mkAnd(
            Term.mkForall(x.of(A), Term.mkApp("P", x)),
            Term.mkApp("P", x)
        );
        
        t.typeCheck(sig);
    }
    
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.UndeterminedSort.class)
    public void halfQuantifiedMultiple() {
        Signature sig = Signature.empty()
            .withSorts(A)
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
    @Test(expected = fortress.data.TypeCheckException.UndeclaredSort.class)
    public void nonExistentSortQuantifier() {
        Signature sig = Signature.empty();
        Term t = Term.mkForall(x.of(A), Term.mkTop());
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.UnknownFunction.class)
    public void functionWrongArity() {
        // Application of function to wrong number of arguments
        Signature sig = Signature.empty()
            .withSort(A)
            .withConstant(x.of(A));
        Term t = Term.mkApp("f", x, x);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.UndeclaredSort.class)
    public void domainElementUnknownSort() {
        // Use a domain element of an undeclared type
        Signature sig = Signature.empty()
            .withSorts(A);
        Term t = Term.mkDomainElement(2, B);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongSort.class)
    public void domainElementSortBool() {
        // Use a domain element of type Bool
        Signature sig = Signature.empty()
            .withSort(A);
        Term t = Term.mkDomainElement(2, Sort.Bool());
        t.typeCheck(sig);
    }
    
    
}
