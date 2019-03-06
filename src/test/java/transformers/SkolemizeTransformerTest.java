import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.transformers.*;

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
    
    Theory baseTheory = Theory.empty()
        .withType(A)
        .withType(B)
        .withConstant(p.of(Type.Bool))
        .withConstant(q.of(Type.Bool))
        .withFunctionDeclaration(f)
        .withFunctionDeclaration(P)
        .withFunctionDeclaration(Q)
        .withFunctionDeclaration(R);
    
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
    public void dualSkolemFunctions() {
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
    
    @Test
    @Ignore ("Test not yet implemented")
    public void onlyUsedVars() {
        
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void multiVariableQuantifier() {
        
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void nameGeneration() {
        
    }
}
