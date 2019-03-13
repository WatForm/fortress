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
    
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, A);
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Type.Bool);
    FuncDecl Q = FuncDecl.mkFuncDecl("Q", B, Type.Bool);
    FuncDecl R = FuncDecl.mkFuncDecl("R", A, B, Type.Bool);
    
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
        .withConstant(p.of(Type.Bool))
        .withConstant(q.of(Type.Bool))
        .withFunctionDeclaration(f)
        .withFunctionDeclaration(P)
        .withFunctionDeclaration(Q)
        .withFunctionDeclaration(R);
    
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
    @Ignore ("Test not yet implemented")
    public void nestedOneType() {
        
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void nestedTwoTypes() {
        
    }
}
