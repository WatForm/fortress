import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;

public class NamingTypeCheckTest {
    
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
    
    // Naming tests
    
    // TODO need more tests of this style
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.NameConflict.class)
    public void clashingVarFunction() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(P);
        Var xp = Term.mkVar("P"); // name clashes with function name
        Term t = Term.mkForall(xp.of(Type.Bool()), xp);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.NameConflict.class)
    public void clashingVarType() {
        Signature sig = Signature.empty()
            .withTypes(A)
            .withConstants()
            .withFunctionDeclarations(P);
        Var xp = Term.mkVar("A"); // name clashes with type name
        Term t = Term.mkForall(xp.of(Type.Bool()), xp);
        t.typeCheck(sig);
    }
    
    
    @Test
    @Ignore ("Test not yet implemented")
    public void varFAddFuncF() {
        // Have a variable named F, then add a function named F
    }
}
