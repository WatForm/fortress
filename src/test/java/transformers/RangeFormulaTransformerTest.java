import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.transformers.*;
import java.util.Map;
import java.util.List;

public class RangeFormulaTransformerTest {
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var c = Term.mkVar("c");
    Var c_1 = Term.mkVar("c_1");
    Var c_2 = Term.mkVar("c_2");
    Var c_3 = Term.mkVar("c_3");
    
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, A);
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Type.Bool);
    FuncDecl Q = FuncDecl.mkFuncDecl("Q", B, Type.Bool);
    FuncDecl R = FuncDecl.mkFuncDecl("R", A, B, Type.Bool);
    
    Var a_1 = Term.mkVar("a_1");
    Var a_2 = Term.mkVar("a_2");
    Var a_3 = Term.mkVar("a_3");
    
    
    
    @Test
    public void basicOneConst() {
        Map<Type, Integer> scopes = Map.of(A, 2);
        RangeFormulaTransformer rf = new RangeFormulaTransformer(scopes);
        
        Theory theory = Theory.empty()
            .withType(A)
            .withFunctionDeclaration(P)
            .withConstant(c.of(A))
            .withAxiom(Term.mkApp("P", c));
        
        Theory expectedResult = Theory.empty()
            .withType(A)
            .withFunctionDeclaration(P)
            .withConstant(c.of(A))
            .withAxiom(Term.mkApp("P", c))
            .withConstant(a_1.of(A))
            .withConstant(a_2.of(A))
            .withAxiom(Term.mkDistinct(a_1, a_2))
            .withAxiom(Term.mkEq(c, a_1));
            
        assertEquals(expectedResult, rf.apply(theory));
    }
    
    @Test
    @Ignore ("test not yet implemented")
    public void basicTwoConst() {
        
    }
    
    @Test
    @Ignore ("test not yet implemented")
    public void quantifiers() {
        
    }
    
    @Test
    @Ignore ("test not yet implemented")
    public void functions() {
        
    }
    
    @Test
    @Ignore ("test not yet implemented")
    public void functionsAndQuantifiers() {
        
    }
    
    @Test
    @Ignore ("test not yet implemented")
    public void scopeOfOne() {
        
    }
}
