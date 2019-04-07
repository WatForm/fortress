import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.transformers.*;
import java.util.Map;
import java.util.List;

public class GroundRangeTransformerTest {
    
    // NOTE: these tests rely upon the implementation detail that 
    // constants are symmetry-broken by insertion order
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    Var c = Term.mkVar("c");
    Var c_1 = Term.mkVar("c_1");
    Var c_2 = Term.mkVar("c_2");
    Var c_3 = Term.mkVar("c_3");
    Var d = Term.mkVar("d");
    Var d_1 = Term.mkVar("d_1");
    Var d_2 = Term.mkVar("d_2");
    Var d_3 = Term.mkVar("d_3");
    
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, A);
    FuncDecl g = FuncDecl.mkFuncDecl("g", B, B);
    FuncDecl h = FuncDecl.mkFuncDecl("h", A, B);
    FuncDecl k = FuncDecl.mkFuncDecl("k", B, A);
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Type.Bool());
    FuncDecl Q = FuncDecl.mkFuncDecl("Q", B, Type.Bool());
    FuncDecl R = FuncDecl.mkFuncDecl("R", A, B, Type.Bool());
    
    Var a_1 = Term.mkVar("a_1");
    Var a_2 = Term.mkVar("a_2");
    Var a_3 = Term.mkVar("a_3");
    
    Var b_1 = Term.mkVar("b_1");
    Var b_2 = Term.mkVar("b_2");
    Var b_3 = Term.mkVar("b_3");
    
    @Test
    public void basicOneConst() {
        Map<Type, Integer> scopes = Map.of(A, 2);
        GroundRangeFormulaTransformer rf = new GroundRangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withType(A)
            .withFunctionDeclaration(P)
            .withConstant(c.of(A))
            .withAxiom(Term.mkApp("P", c));
        
        Theory expected = Theory.empty()
            .withType(A)
            .withFunctionDeclaration(P)
            .withConstant(c.of(A))
            .withAxiom(Term.mkApp("P", c))
            // New
            .withConstant(a_1.of(A))
            .withConstant(a_2.of(A))
            .withAxiom(Term.mkDistinct(a_1, a_2))
            .withAxiom(Term.mkEq(c, a_1));
            
        assertEquals(expected, rf.apply(theory));
    }
    
    @Test
    public void basicManyConst() {
        Map<Type, Integer> scopes = Map.of(A, 2);
        GroundRangeFormulaTransformer rf = new GroundRangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withType(A)
            .withFunctionDeclaration(P)
            .withConstants(c_1.of(A), c_2.of(A), c_3.of(A))
            .withAxiom(Term.mkApp("P", c_1))
            .withAxiom(Term.mkApp("P", c_2))
            .withAxiom(Term.mkApp("P", c_3));
        
        Theory expected = Theory.empty()
            .withType(A)
            .withFunctionDeclaration(P)
            .withConstants(c_1.of(A), c_2.of(A), c_3.of(A))
            .withAxiom(Term.mkApp("P", c_1))
            .withAxiom(Term.mkApp("P", c_2))
            .withAxiom(Term.mkApp("P", c_3))
            // New
            .withConstants(a_1.of(A), a_2.of(A))
            .withAxiom(Term.mkDistinct(a_1, a_2))
            .withAxiom(Term.mkEq(c_1, a_1))
            .withAxiom(Term.mkOr(Term.mkEq(c_2, a_1), Term.mkEq(c_2, a_2)))
            .withAxiom(Term.mkOr(Term.mkEq(c_3, a_1), Term.mkEq(c_3, a_2)));
            
        assertEquals(expected, rf.apply(theory));
    }
    
    @Test
    public void multipleTypesConsts() {
        Map<Type, Integer> scopes = Map.of(A, 2, B, 3);
        GroundRangeFormulaTransformer rf = new GroundRangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withTypes(A, B)
            .withFunctionDeclarations(P, Q)
            .withConstants(c_1.of(A), c_2.of(A), c_3.of(A))
            .withConstants(d_1.of(B), d_2.of(B), d_3.of(B))
            .withAxiom(Term.mkApp("P", c_1))
            .withAxiom(Term.mkApp("Q", d_3));
        
        Theory expected = theory
            .withConstants(a_1.of(A), a_2.of(A))
            .withConstants(b_1.of(B), b_2.of(B), b_3.of(B))
            .withAxiom(Term.mkDistinct(a_1, a_2))
            .withAxiom(Term.mkDistinct(b_1, b_2, b_3))
            .withAxiom(Term.mkEq(c_1, a_1))
            .withAxiom(Term.mkOr(Term.mkEq(c_2, a_1), Term.mkEq(c_2, a_2)))
            .withAxiom(Term.mkOr(Term.mkEq(c_3, a_1), Term.mkEq(c_3, a_2)))
            .withAxiom(Term.mkEq(d_1, b_1))
            .withAxiom(Term.mkOr(Term.mkEq(d_2, b_1), Term.mkEq(d_2, b_2)))
            .withAxiom(Term.mkOr(Term.mkEq(d_3, b_1), Term.mkEq(d_3, b_2), Term.mkEq(d_3, b_3)));
        
        assertEquals(expected, rf.apply(theory));
    }
    
    @Test
    public void quantifiers() {
        Map<Type, Integer> scopes = Map.of(A, 2, B, 3);
        GroundRangeFormulaTransformer rf = new GroundRangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withTypes(A, B)
            .withFunctionDeclarations(P, Q)
            .withConstants(c_1.of(A), c_2.of(A))
            .withConstants(d_1.of(B), d_2.of(B))
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("P", x)))
            .withAxiom(Term.mkForall(y.of(B), Term.mkApp("Q", y)));
        
        Theory expected = Theory.empty()
            .withTypes(A, B)
            .withFunctionDeclarations(P, Q)
            .withConstants(c_1.of(A), c_2.of(A))
            .withConstants(d_1.of(B), d_2.of(B))
            // New
            .withConstants(a_1.of(A), a_2.of(A))
            .withConstants(b_1.of(B), b_2.of(B), b_3.of(B))
            .withAxiom(Term.mkDistinct(a_1, a_2))
            .withAxiom(Term.mkDistinct(b_1, b_2, b_3))
            .withAxiom(Term.mkAnd(
                Term.mkApp("P", a_1),
                Term.mkApp("P", a_2)))
            .withAxiom(Term.mkAnd(
                Term.mkApp("Q", b_1),
                Term.mkApp("Q", b_2),
                Term.mkApp("Q", b_3)))
            // Range constraints
            .withAxiom(Term.mkEq(c_1, a_1))
            .withAxiom(Term.mkOr(Term.mkEq(c_2, a_1), Term.mkEq(c_2, a_2)))
            .withAxiom(Term.mkEq(d_1, b_1))
            .withAxiom(Term.mkOr(Term.mkEq(d_2, b_1), Term.mkEq(d_2, b_2)));
            
       assertEquals(expected, rf.apply(theory));
    }
    
    @Test
    public void functions() {
        Map<Type, Integer> scopes = Map.of(A, 2, B, 3);
        GroundRangeFormulaTransformer rf = new GroundRangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withTypes(A, B)
            .withConstants(c_1.of(A))
            .withConstants(d_1.of(B))
            .withFunctionDeclarations(P, Q, f, g, h, k)
            .withAxiom(Term.mkEq(Term.mkApp("f", c_1), Term.mkApp("k", d_1)))
            .withAxiom(Term.mkApp("Q", Term.mkApp("g", d_1)))
            .withAxiom(Term.mkApp("Q", Term.mkApp("h", c_1)));
        
        Term f_a1 = Term.mkApp("f", a_1);
        Term f_a2 = Term.mkApp("f", a_2);
        Term g_b1 = Term.mkApp("g", b_1);
        Term g_b2 = Term.mkApp("g", b_2);
        Term g_b3 = Term.mkApp("g", b_3);
        Term h_a1 = Term.mkApp("h", a_1);
        Term h_a2 = Term.mkApp("h", a_2);
        Term k_b1 = Term.mkApp("k", b_1);
        Term k_b2 = Term.mkApp("k", b_2);
        Term k_b3 = Term.mkApp("k", b_3);
        
        Theory expected = theory
            .withConstants(a_1.of(A), a_2.of(A))
            .withConstants(b_1.of(B), b_2.of(B), b_3.of(B))
            .withAxiom(Term.mkDistinct(a_1, a_2))
            .withAxiom(Term.mkDistinct(b_1, b_2, b_3))
            // Range constraints for constants
            .withAxiom(Term.mkEq(c_1, a_1))
            .withAxiom(Term.mkEq(d_1, b_1))
            // Range constraints for functions, NOT symmetry broken
            // f
            .withAxiom(Term.mkOr(Term.mkEq(f_a1, a_1), Term.mkEq(f_a1, a_2)))
            .withAxiom(Term.mkOr(Term.mkEq(f_a2, a_1), Term.mkEq(f_a2, a_2)))
            // g
            .withAxiom(Term.mkOr(Term.mkEq(g_b1, b_1), Term.mkEq(g_b1, b_2), Term.mkEq(g_b1, b_3)))
            .withAxiom(Term.mkOr(Term.mkEq(g_b2, b_1), Term.mkEq(g_b2, b_2), Term.mkEq(g_b2, b_3)))
            .withAxiom(Term.mkOr(Term.mkEq(g_b3, b_1), Term.mkEq(g_b3, b_2), Term.mkEq(g_b3, b_3)))
            // h
            .withAxiom(Term.mkOr(Term.mkEq(h_a1, b_1), Term.mkEq(h_a1, b_2), Term.mkEq(h_a1, b_3)))
            .withAxiom(Term.mkOr(Term.mkEq(h_a2, b_1), Term.mkEq(h_a2, b_2), Term.mkEq(h_a2, b_3)))
            // k
            .withAxiom(Term.mkOr(Term.mkEq(k_b1, a_1), Term.mkEq(k_b1, a_2)))
            .withAxiom(Term.mkOr(Term.mkEq(k_b2, a_1), Term.mkEq(k_b2, a_2)))
            .withAxiom(Term.mkOr(Term.mkEq(k_b3, a_1), Term.mkEq(k_b3, a_2)));
        
        assertEquals(expected, rf.apply(theory));
    }
    
    @Test
    public void functionsAndQuantifiers() {
        Map<Type, Integer> scopes = Map.of(A, 2, B, 2);
        GroundRangeFormulaTransformer rf = new GroundRangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withTypes(A, B)
            .withFunctionDeclarations(P, f, g)
            .withConstants(c_1.of(A))
            .withAxiom(Term.mkForall(x.of(A), Term.mkOr(Term.mkEq(x, c_1), Term.mkApp("P", Term.mkApp("f", x)))))
            .withAxiom(Term.mkForall(List.of(y.of(B), z.of(B)),
                Term.mkOr(Term.mkEq(y, z),
                    Term.mkNot(Term.mkEq(Term.mkApp("g", y), Term.mkApp("g", z))))));
        
        Term f_a1 = Term.mkApp("f", a_1);
        Term f_a2 = Term.mkApp("f", a_2);
        Term g_b1 = Term.mkApp("g", b_1);
        Term g_b2 = Term.mkApp("g", b_2);
        
        Theory expected = Theory.empty()
            .withTypes(A, B)
            .withFunctionDeclarations(P, f, g)
            .withConstants(c_1.of(A))
            // New
            .withConstants(a_1.of(A), a_2.of(A))
            .withConstants(b_1.of(B), b_2.of(B))
            .withAxiom(Term.mkDistinct(a_1, a_2))
            .withAxiom(Term.mkDistinct(b_1, b_2))
            .withAxiom(Term.mkAnd(
                Term.mkOr(Term.mkEq(a_1, c_1), Term.mkApp("P", Term.mkApp("f", a_1))),
                Term.mkOr(Term.mkEq(a_2, c_1), Term.mkApp("P", Term.mkApp("f", a_2)))
            ))
            .withAxiom(Term.mkAnd(
                Term.mkOr(Term.mkEq(b_1, b_1), Term.mkNot(Term.mkEq(Term.mkApp("g", b_1), Term.mkApp("g", b_1)))),
                Term.mkOr(Term.mkEq(b_2, b_1), Term.mkNot(Term.mkEq(Term.mkApp("g", b_2), Term.mkApp("g", b_1)))),
                Term.mkOr(Term.mkEq(b_1, b_2), Term.mkNot(Term.mkEq(Term.mkApp("g", b_1), Term.mkApp("g", b_2)))),
                Term.mkOr(Term.mkEq(b_2, b_2), Term.mkNot(Term.mkEq(Term.mkApp("g", b_2), Term.mkApp("g", b_2))))
            ))
            // Range constraints for constants
            .withAxiom(Term.mkEq(c_1, a_1))
            // Range constraints for functions, NOT symmetry broken
            // f
            .withAxiom(Term.mkOr(Term.mkEq(f_a1, a_1), Term.mkEq(f_a1, a_2)))
            .withAxiom(Term.mkOr(Term.mkEq(f_a2, a_1), Term.mkEq(f_a2, a_2)))
            // g
            .withAxiom(Term.mkOr(Term.mkEq(g_b1, b_1), Term.mkEq(g_b1, b_2)))
            .withAxiom(Term.mkOr(Term.mkEq(g_b2, b_1), Term.mkEq(g_b2, b_2)));
            
        assertEquals(expected, rf.apply(theory));
    }
    
    @Test
    public void scopeOfOne() {
        Map<Type, Integer> scopes = Map.of(A, 1);
        GroundRangeFormulaTransformer rf = new GroundRangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withTypes(A)
            .withFunctionDeclaration(P)
            .withConstants(c_1.of(A), c_2.of(A))
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("P", x)));
        
        Theory expected = Theory.empty()
            .withTypes(A)
            .withFunctionDeclaration(P)
            .withConstants(c_1.of(A), c_2.of(A))
            // New
            .withConstant(a_1.of(A))
            .withAxiom(Term.mkApp("P", a_1))
            // Range constaints
            .withAxiom(Term.mkEq(c_1, a_1))
            .withAxiom(Term.mkEq(c_2, a_1));
        
        assertEquals(expected, rf.apply(theory));
    }
    
    @Test
    public void booleanConstantsNotRestricted() {
        Map<Type, Integer> scopes = Map.of(A, 1);
        GroundRangeFormulaTransformer rf = new GroundRangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withType(A)
            .withFunctionDeclaration(P)
            .withConstants(q.of(Type.Bool()), c.of(A))
            .withAxiom(q)
            .withAxiom(Term.mkApp("P", c));
        
        Theory expected = theory
            .withConstant(a_1.of(A))
            .withAxiom(Term.mkEq(c, a_1));
        
        assertEquals(expected, rf.apply(theory));
    }
    
    @Test
    public void unlistedTypeNotExpanded() {
        Map<Type, Integer> scopes = Map.of(A, 1);
        GroundRangeFormulaTransformer rf = new GroundRangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withTypes(A, B)
            .withFunctionDeclarations(P, Q)
            .withConstants(c.of(A), d.of(B))
            .withAxiom(Term.mkApp("P", c))
            .withAxiom(Term.mkApp("Q", d));
        
        Theory expected = theory
            .withConstant(a_1.of(A))
            .withAxiom(Term.mkEq(c, a_1));
        
        assertEquals(expected, rf.apply(theory));
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void unlistedTypeNotExpanded2() {
        
    }
    
    // Usage tests
    
    @Test 
    @Ignore ("Test not yet implemented")
    public void extraTypeScopeFails() {
        
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void booleanScopeFails() {
        
    }
}
