import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.transformers.*;
import java.util.Map;
import java.util.List;

public class GroundingTransformerTest {
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    Var c_1 = Term.mkVar("c_1");
    Var c_2 = Term.mkVar("c_2");
    
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, A);
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Type.Bool());
    FuncDecl Q = FuncDecl.mkFuncDecl("Q", B, Type.Bool());
    FuncDecl R = FuncDecl.mkFuncDecl("R", A, B, Type.Bool());
    FuncDecl S = FuncDecl.mkFuncDecl("S", A, A, Type.Bool());
    FuncDecl T = FuncDecl.mkFuncDecl("T", A, A, A, Type.Bool());
    
    Var a_1 = Term.mkVar("a_1");
    Var a_2 = Term.mkVar("a_2");
    Var b_1 = Term.mkVar("b_1");
    Var b_2 = Term.mkVar("b_2");
        
    Map<Type, List<Var>> typeInstantiations = Map.of(
        A, List.of(a_1, a_2),
        B, List.of(b_1, b_2)
    );
    
    TheoryTransformer grounding = new GroundingTransformer(typeInstantiations);
    
    Theory baseTheory = Theory.empty()
        .withType(A)
        .withType(B)
        .withConstant(p.of(Type.Bool()))
        .withConstant(q.of(Type.Bool()))
        .withFunctionDeclaration(f)
        .withFunctionDeclaration(P)
        .withFunctionDeclaration(Q)
        .withFunctionDeclaration(R)
        .withFunctionDeclaration(S)
        .withFunctionDeclaration(T);
    
    Theory baseExpectedTheory = baseTheory
        .withConstant(a_1.of(A))
        .withConstant(a_2.of(A))
        .withConstant(b_1.of(B))
        .withConstant(b_2.of(B));
    
    @Test
    public void basicOneType() {
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("P", x)));
        
        Theory expected = baseExpectedTheory
            .withAxiom(Term.mkAnd(Term.mkApp("P", a_1), Term.mkApp("P", a_2)));
        
        assertEquals(expected, grounding.apply(theory));
    }
    
    @Test
    public void basicTwoTypes() {
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(
                List.of(x.of(A), y.of(B)),
                Term.mkApp("R", x, y)));
        
        Theory expected = baseExpectedTheory
            .withAxiom(Term.mkAnd(
                Term.mkApp("R", a_1, b_1),
                Term.mkApp("R", a_2, b_1),
                Term.mkApp("R", a_1, b_2),
                Term.mkApp("R", a_2, b_2)));
        
        assertEquals(expected, grounding.apply(theory));
    }
    
    @Test
    public void constantsNotInstantiated() {
        Theory theory = baseTheory
            .withConstant(x.of(A))
            .withAxiom(Term.mkForall(y.of(B), Term.mkApp("R", x, y)));
        
        Theory expected = baseExpectedTheory
            .withConstant(x.of(A))
            .withAxiom(Term.mkAnd(
                Term.mkApp("R", x, b_1),
                Term.mkApp("R", x, b_2)));
        
        assertEquals(expected, grounding.apply(theory));
    }
    
    @Test
    public void nested() {
        // Same whether you instantiate top down or bottom up
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(x.of(A),Term.mkOr(
                Term.mkForall(y.of(A),Term.mkApp("S", x, y)),
                Term.mkForall(z.of(B), Term.mkApp("R", x, z)))));
        
        Term _11y = Term.mkApp("S", a_1, a_1);
        Term _12y = Term.mkApp("S", a_1, a_2);
        Term _21y = Term.mkApp("S", a_2, a_1);
        Term _22y = Term.mkApp("S", a_2, a_2);
        
        Term _11z = Term.mkApp("R", a_1, b_1);
        Term _12z = Term.mkApp("R", a_1, b_2);
        Term _21z = Term.mkApp("R", a_2, b_1);
        Term _22z = Term.mkApp("R", a_2, b_2);
        
        Term t1 = Term.mkOr(
            Term.mkAnd(_11y, _12y),
            Term.mkAnd(_11z, _12z)
        );
        Term t2 = Term.mkOr(
            Term.mkAnd(_21y, _22y),
            Term.mkAnd(_21z, _22z)
        );
        
        Theory expected = baseExpectedTheory
            .withAxiom(Term.mkAnd(t1, t2));
        
        assertEquals(expected, grounding.apply(theory));
    }
    
    @Test
    public void multiVarQuantifier() {
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(List.of(x.of(A), y.of(A)),
                Term.mkOr(
                    Term.mkApp("S", x, y),
                    Term.mkForall(z.of(A), Term.mkApp("T", x, y, z)))));
        
        Theory expected = baseTheory
            .withConstants(a_1.of(A), a_2.of(A))
            .withAxiom(Term.mkAnd(
                Term.mkOr(Term.mkApp("S", a_1, a_1), Term.mkAnd(Term.mkApp("T", a_1, a_1, a_1), Term.mkApp("T", a_1, a_1, a_2))),
                Term.mkOr(Term.mkApp("S", a_2, a_1), Term.mkAnd(Term.mkApp("T", a_2, a_1, a_1), Term.mkApp("T", a_2, a_1, a_2))),
                Term.mkOr(Term.mkApp("S", a_1, a_2), Term.mkAnd(Term.mkApp("T", a_1, a_2, a_1), Term.mkApp("T", a_1, a_2, a_2))),
                Term.mkOr(Term.mkApp("S", a_2, a_2), Term.mkAnd(Term.mkApp("T", a_2, a_2, a_1), Term.mkApp("T", a_2, a_2, a_2)))));
        
        TheoryTransformer grounding = new GroundingTransformer(Map.of(A, List.of(a_1, a_2)));
        assertEquals(expected, grounding.apply(theory));
    }
    
    @Test
    public void scopeSizeOne() {
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(x.of(A),Term.mkOr(
                Term.mkForall(y.of(A),Term.mkApp("S", x, y)),
                Term.mkForall(z.of(B), Term.mkApp("R", x, z)))));
        
        Theory expected = baseTheory
            .withConstant(a_1.of(A))
            .withConstant(b_1.of(B))
            .withAxiom(Term.mkOr(Term.mkApp("S", a_1, a_1), Term.mkApp("R", a_1, b_1)));
        
        assertEquals(expected, new GroundingTransformer(Map.of(A, List.of(a_1), B, List.of(b_1))).apply(theory));
    }
    
    @Test
    // Former bug
    public void negationBug0() {
        Theory theory = Theory.empty()
            .withTypes(A)
            .withFunctionDeclaration(P)
            .withAxiom(Term.mkForall(y.of(A),
                    Term.mkNot(Term.mkApp("P", y))));
                    
        Theory expected = Theory.empty()
            .withTypes(A)
            .withFunctionDeclaration(P)
            // New
            .withConstants(a_1.of(A))
            .withAxiom(Term.mkNot(Term.mkApp("P", a_1)));
        
        assertEquals(expected, new GroundingTransformer(Map.of(A, List.of(a_1))).apply(theory));
    }
    
    @Test
    // Former bug
    public void negationBug1() {
        Theory theory = Theory.empty()
            .withTypes(A)
            .withFunctionDeclaration(f)
            .withAxiom(Term.mkForall(List.of(y.of(A), z.of(A)),
                Term.mkOr(Term.mkEq(y, z),
                    Term.mkNot(Term.mkEq(Term.mkApp("f", y), Term.mkApp("f", z))))));
                    
        Theory expected = Theory.empty()
            .withTypes(A)
            .withFunctionDeclaration(f)
            // New
            .withConstants(a_1.of(A), a_2.of(A))
            .withAxiom(Term.mkAnd(
                Term.mkOr(Term.mkEq(a_1, a_1), Term.mkNot(Term.mkEq(Term.mkApp("f", a_1), Term.mkApp("f", a_1)))),
                Term.mkOr(Term.mkEq(a_2, a_1), Term.mkNot(Term.mkEq(Term.mkApp("f", a_2), Term.mkApp("f", a_1)))),
                Term.mkOr(Term.mkEq(a_1, a_2), Term.mkNot(Term.mkEq(Term.mkApp("f", a_1), Term.mkApp("f", a_2)))),
                Term.mkOr(Term.mkEq(a_2, a_2), Term.mkNot(Term.mkEq(Term.mkApp("f", a_2), Term.mkApp("f", a_2))))
            ));
        
        assertEquals(expected, new GroundingTransformer(Map.of(A, List.of(a_1, a_2))).apply(theory));
    }
    
}
