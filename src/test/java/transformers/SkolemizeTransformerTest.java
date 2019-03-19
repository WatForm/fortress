import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.*;

import fortress.tfol.*;
import fortress.transformers.*;
import java.util.List;

public class SkolemizeTransformerTest {
    
    TheoryTransformer skolemizer = new SkolemizeTransformer();
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, A);
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Type.Bool);
    FuncDecl Q = FuncDecl.mkFuncDecl("Q", A, A, Type.Bool);
    FuncDecl R = FuncDecl.mkFuncDecl("R", A, A, A, Type.Bool);
    FuncDecl S = FuncDecl.mkFuncDecl("S", B, Type.Bool);
    FuncDecl T = FuncDecl.mkFuncDecl("T", A, B, Type.Bool);
    FuncDecl R_1 = FuncDecl.mkFuncDecl("R_1", A, A, B, Type.Bool);
    
    Theory baseTheory = Theory.empty()
        .withType(A)
        .withType(B)
        .withConstant(p.of(Type.Bool))
        .withConstant(q.of(Type.Bool))
        .withFunctionDeclaration(f)
        .withFunctionDeclaration(P)
        .withFunctionDeclaration(Q)
        .withFunctionDeclaration(R)
        .withFunctionDeclaration(S)
        .withFunctionDeclaration(T)
        .withFunctionDeclaration(R_1);
    
    @Test
    public void simpleSkolemConstant() {
        Theory theory = baseTheory
            .withAxiom(Term.mkExists(y.of(A), Term.mkApp("P", y)));

        Theory expected = baseTheory
            .withConstant(Term.mkVar("sk_0").of(A))
            .withAxiom(Term.mkApp("P", Term.mkVar("sk_0")));
            
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    @Test
    public void simpleSkolemFunction() {
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(x.of(A), Term.mkExists(y.of(A), Term.mkApp("Q", x, y))));
        
        Theory expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("Q", x, Term.mkApp("sk_0", x))));
            
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    @Test
    public void allExistsAll() {
        // z should not be part of the skolem function
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(x.of(A), Term.mkExists(y.of(A), Term.mkForall(z.of(A), Term.mkApp("R", x, y, z)))));
        
        Theory expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withAxiom(Term.mkForall(x.of(A), Term.mkForall(z.of(A), Term.mkApp("R", x, Term.mkApp("sk_0", x), z))));
            
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    @Test
    public void multipleSkolemFunctions() {
        Theory theory = baseTheory
            .withAxiom(Term.mkAnd(
                Term.mkForall(x.of(A), Term.mkExists(y.of(A), Term.mkApp("Q", x, y))),
                Term.mkForall(z.of(A), Term.mkExists(y.of(A), Term.mkApp("Q", y, z))),
                Term.mkExists(y.of(A), Term.mkApp("P", y))));
        
        Theory expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, A))
            .withConstant(Term.mkVar("sk_2").of(A))
            .withAxiom(Term.mkAnd(
                Term.mkForall(x.of(A), Term.mkApp("Q", x, Term.mkApp("sk_0", x))),
                Term.mkForall(z.of(A), Term.mkApp("Q", Term.mkApp("sk_1", z), z)),
                Term.mkApp("P", Term.mkVar("sk_2"))));
        
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    // TODO how to test when technically the order of arguments is not guaranteed?
    // Will just have to do either or
    
    @Test
    // Only the free variables actually used should be made as arguments to the skolem function
    public void onlyUsedVars1() {
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(x.of(A), Term.mkExists(y.of(B), Term.mkApp("S", y))));
        
        Theory expected = baseTheory
            .withConstant(Term.mkVar("sk_0").of(B))
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("S", Term.mkVar("sk_0"))));
            
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    @Test
    // Only the free variables actually used should be made as arguments to the skolem function
    public void onlyUsedVars2() {
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(List.of(x.of(A), z.of(A)), Term.mkExists(y.of(B), Term.mkApp("T", z, y))));
        
        Theory expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, B))
            .withAxiom(Term.mkForall(List.of(x.of(A), z.of(A)), Term.mkApp("T", z, Term.mkApp("sk_0", z))));
            
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    @Test
    public void multiVariableExists() {
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(x.of(A), Term.mkExists(List.of(y.of(A), z.of(A)), Term.mkApp("R", x, y, z))));
        
        Theory expected = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, A))
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("R", x, Term.mkApp("sk_0", x), Term.mkApp("sk_1", x))));
        
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    @Test
    public void multiArgument() {
        Theory theory = baseTheory
            .withAxiom(Term.mkForall(List.of(x.of(A), z.of(B)), Term.mkExists(y.of(A), Term.mkApp("R_1", x, y, z))));
        
        // We don't specify which order of arguments the skolem function must use,
        // so either of the following is acceptable
        
        Theory expected1 = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, B, A))
            .withAxiom(Term.mkForall(List.of(x.of(A), z.of(B)), Term.mkApp("R_1", x, Term.mkApp("sk_0", x, z), z)));
        
        Theory expected2 = baseTheory
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", B, A, A))
            .withAxiom(Term.mkForall(List.of(x.of(A), z.of(B)), Term.mkApp("R_1", x, Term.mkApp("sk_0", z, x), z)));
        
        assertThat(skolemizer.apply(theory), anyOf(is(expected1), is(expected2)));
    }
    
    @Test
    // Constants should not be included as arguments to skolem functions
    public void notIncludeConstants() {
        Theory theory = baseTheory
            .withConstant(z.of(B))
            .withAxiom(Term.mkForall(x.of(A), Term.mkExists(y.of(A), Term.mkApp("R_1", x, y, z))));
        
        Theory expected = baseTheory
            .withConstant(z.of(B))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("R_1", x, Term.mkApp("sk_0", x), z)));
        
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    @Test
    public void existsForallExists() {
        Theory theory = baseTheory
            .withAxiom(Term.mkExists(y.of(A), Term.mkForall(x.of(A), Term.mkExists(z.of(A), Term.mkApp("R", x, y, z)))));
        
        Theory expected = baseTheory
            .withConstant(Term.mkVar("sk_0").of(A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, A))
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("R", x, Term.mkVar("sk_0"), Term.mkApp("sk_1", x))));
        
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    @Test
    public void nameGeneration() {
        // The names sk_0, sk_1, sk_2, sk_4, sk_5 are used
        // The next names should be sk_3 and sk_6
        Theory theory = baseTheory
            .withType(Type.mkTypeConst("sk_0"))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, Type.Bool))
            .withConstant(Term.mkVar("sk_2").of(A))
            .withAxiom(Term.mkForall(Term.mkVar("sk_4").of(A), Term.mkTop()))
            .withAxiom(Term.mkForall(Term.mkVar("sk_5").of(A), Term.mkTop()))
            .withAxiom(Term.mkAnd(
                Term.mkExists(y.of(A), Term.mkApp("P", y)),
                Term.mkForall(x.of(A), Term.mkExists(y.of(A), Term.mkApp("Q", x, y)))));
                
        Theory expected = baseTheory
            .withType(Type.mkTypeConst("sk_0"))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, Type.Bool))
            .withConstant(Term.mkVar("sk_2").of(A))
            .withAxiom(Term.mkForall(Term.mkVar("sk_4").of(A), Term.mkTop()))
            .withAxiom(Term.mkForall(Term.mkVar("sk_5").of(A), Term.mkTop()))
            .withConstant(Term.mkVar("sk_3").of(A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_6", A, A))
            .withAxiom(Term.mkAnd(
                Term.mkApp("P", Term.mkVar("sk_3")),
                Term.mkForall(x.of(A), Term.mkApp("Q", x, Term.mkApp("sk_6", x)))));
        
        assertEquals(expected, skolemizer.apply(theory));
    }
    
    @Test
    public void multipleFormulas() {
        Theory theory = baseTheory
            .withAxiom(Term.mkExists(y.of(A), Term.mkApp("P", y)))
            .withAxiom(Term.mkForall(x.of(A), Term.mkExists(y.of(A), Term.mkApp("Q", x, y))));
        
        // Either of the following is acceptable
        Theory expected1 = baseTheory
            .withConstant(Term.mkVar("sk_0").of(A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_1", A, A))
            .withAxiom(Term.mkApp("P", Term.mkVar("sk_0")))
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("Q", x, Term.mkApp("sk_1", x))));
        
        Theory expected2 = baseTheory
            .withConstant(Term.mkVar("sk_1").of(A))
            .withFunctionDeclaration(FuncDecl.mkFuncDecl("sk_0", A, A))
            .withAxiom(Term.mkApp("P", Term.mkVar("sk_1")))
            .withAxiom(Term.mkForall(x.of(A), Term.mkApp("Q", x, Term.mkApp("sk_0", x))));
        
        assertThat(skolemizer.apply(theory), anyOf(is(expected1), is(expected2)));
    }
}
