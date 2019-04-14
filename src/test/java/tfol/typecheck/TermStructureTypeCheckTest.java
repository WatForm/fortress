import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;

public class TermStructureTypeCheckTest {
    
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
    
    // Term structure
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void forallInsideApp() {
        // Forall is not allowed inside an application
        Signature sig = Signature.empty()
            .withTypes(A)
            .withFunctionDeclarations(h);
        Term t = Term.mkApp("h", Term.mkForall(x.of(A), Term.mkTop()));
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void existsInsideApp() {
        // Exists is not allowed inside an application
        Signature sig = Signature.empty()
            .withTypes(A)
            .withFunctionDeclarations(h);
        Term t = Term.mkApp("h", Term.mkExists(x.of(A), Term.mkTop()));
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void connectiveInsideApp() {
        // Logical connectives are not allowed inside an application
        Signature sig = Signature.empty()
            .withFunctionDeclaration(h);
        Term t = Term.mkApp("h", Term.mkAnd(Term.mkTop(), Term.mkTop()));
        t.typeCheck(sig);
            
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void negationInsideApp() {
        // Negation is not allowed inside an application
        Signature sig = Signature.empty()
            .withFunctionDeclaration(h);
        Term t = Term.mkApp("h", Term.mkNot(Term.mkTop()));
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void equalsInsideApp() {
        // = is not allowed inside an application
        Signature sig = Signature.empty()
            .withType(A)
            .withConstant(x.of(A))
            .withFunctionDeclaration(h);
        Term t = Term.mkApp("h", Term.mkEq(x, x));
        t.typeCheck(sig);
    }
    
    @Test(expected = fortress.data.TypeCheckException.BadStructure.class)
    public void distinctInsideApp() {
        // distinct is not allowed inside an application
        Signature sig = Signature.empty()
            .withType(A)
            .withConstant(x.of(A))
            .withFunctionDeclaration(h);
        Term t = Term.mkApp("h", Term.mkDistinct(x, x));
        t.typeCheck(sig);
    }
}
