import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;

public class NegativeTypeCheckTest {
    
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
    
    FuncDecl transitionRelation = FuncDecl.mkFuncDecl("transition", A, A, Type.Bool());
    FuncDecl transitionFunction = FuncDecl.mkFuncDecl("transition", A, Type.Bool());
    
    
    @Test(expected = fortress.data.TypeCheckException.UndeterminedType.class)
    public void freeVar() {
        // A free var should fail typechecking
        Signature sig = Signature.empty()
            .withType(A)
            .withConstants()
            .withFunctionDeclarations();
        
        x.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void functionAppConstWrongArg() {
        // Application of a function to a constant of the wrong argument type
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(g);
        Term app = Term.mkApp("g", x);
        app.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.UnknownFunction.class)
    public void functionAppConstMissingDecl() {
        // Use of a function that is missing a declaration
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants(x.of(A))
            .withFunctionDeclarations();
        Term app = Term.mkApp("f", x);
        app.typeCheck(sig);
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
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void andWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(Type.Bool()))
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
            .withConstants(x.of(A), y.of(Type.Bool()))
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
            .withConstants(x.of(A), y.of(Type.Bool()))
            .withFunctionDeclarations(f);
        Term arg1 = Term.mkApp("f", x);
        Term arg2 = y;
        Term imp = Term.mkImp(arg1, arg2);
        imp.typeCheck(sig);
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
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void notWrongArg() {
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A))
            .withFunctionDeclarations(f);
        Term not = Term.mkNot(Term.mkApp("f", x));
        not.typeCheck(sig);
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
    
    @Test(expected = fortress.data.TypeCheckException.UndeterminedType.class)
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
    @Test(expected = fortress.data.TypeCheckException.UndeterminedType.class)
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
    
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.UndeterminedType.class)
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
    
    @Test(expected = fortress.data.TypeCheckException.WrongArity.class)
    public void functionWrongArity() {
        // Application of function to wrong number of arguments
        Signature sig = Signature.empty()
            .withType(A)
            .withConstant(x.of(A));
        Term t = Term.mkApp("f", x, x);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void transitiveClosureRelationWrongArg1() {
         // ^P(x, y) where P: A x A -> Bool but x: B
         Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(B), y.of(A))
            .withFunctionDeclaration(transitionRelation);
         Term t = Term.mkTC("transition", x, y);
         t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void transitiveClosureRelationWrongArg2() {
        // ^P(x, y) where P: A x A -> Bool but y: B
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclaration(transitionRelation);
         Term t = Term.mkTC("transition", x, y);
         t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void transitiveClosureFunctionWrongArg1() {
        // ^P(x, y) where P: A -> A but x: B
        Signature sig = Signature.empty()
            .withTypes(A, B)
           .withConstants(x.of(B), y.of(A))
           .withFunctionDeclaration(transitionFunction);
        Term t = Term.mkTC("transition", x, y);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void transitiveClosureFunctionWrongArg2() {
        // ^P(x, y) where P: A -> A but y: B
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(B))
            .withFunctionDeclaration(transitionFunction);
         Term t = Term.mkTC("transition", x, y);
         t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.UnknownFunction.class)
    public void transitiveClosureUnknownRelation() {
        // Transitive closure taken of undeclared relation/function
        Signature sig = Signature.empty()
            .withType(A)
            .withConstants(x.of(A), y.of(A));
        Term t = Term.mkTC("transition", x, y);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void transitiveClosureWrongRelationType1() {
        FuncDecl transition = FuncDecl.mkFuncDecl("transition", A, B, Type.Bool());
        // Transitive colosure of A x B -> Bool, not A x A -> Bool or A -> A
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(A))
            .withFunctionDeclaration(transition);
        Term t = Term.mkTC("transition", x, y);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void transitiveClosureWrongRelationType2() {
        FuncDecl transition = FuncDecl.mkFuncDecl("transition", A, A, A, Type.Bool());
        // Transitive colosure of A x A x A -> Bool, not A x A -> Bool or A -> A
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(A))
            .withFunctionDeclaration(transition);
        Term t = Term.mkTC("transition", x, y);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void transitiveClosureWrongRelationType3() {
        FuncDecl transition = FuncDecl.mkFuncDecl("transition", A, B);
        // Transitive colosure of A -> B, not A x A -> Bool or A -> A
        Signature sig = Signature.empty()
            .withTypes(A, B)
            .withConstants(x.of(A), y.of(A))
            .withFunctionDeclaration(transition);
        Term t = Term.mkTC("transition", x, y);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.UnknownType.class)
    public void domainElementUnkownType() {
        // Use a domain element of an undeclared type
        Signature sig = Signature.empty()
            .withTypes(A);
        Term t = Term.mkDomainElement(2, B);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.WrongArgType.class)
    public void domainElementTypeBool() {
        // Use a domain element of type Bool
        Signature sig = Signature.empty()
            .withType(A);
        Term t = Term.mkDomainElement(2, Type.Bool());
        t.typeCheck(sig);
    }
    
    
}
