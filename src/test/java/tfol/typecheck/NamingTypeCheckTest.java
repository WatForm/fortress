import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;

public class NamingTypeCheckTest {
    
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
    
    // Naming tests
    
    // TODO need more tests of this style
    // Former bug
    @Test(expected = fortress.data.TypeCheckException.NameConflict.class)
    public void clashingVarFunction() {
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants()
            .withFunctionDeclarations(P);
        Var xp = Term.mkVar("P"); // name clashes with function name
        Term t = Term.mkForall(xp.of(Sort.Bool()), xp);
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.NameConflict.class)
    public void clashingVarSort() {
        Signature sig = Signature.empty()
            .withSorts(A)
            .withConstants()
            .withFunctionDeclarations(P);
        Var xp = Term.mkVar("A"); // name clashes with type name
        Term t = Term.mkForall(xp.of(Sort.Bool()), xp);
        t.typeCheck(sig);
    }
    
    
    @Test
    @Ignore ("Test not yet implemented")
    public void varFAddFuncF() {
        // Have a variable named F, then add a function named F
    }
}
