import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.tfol.Term.*;
import fortress.tfol.Type.*;
import fortress.tfol.FuncDecl.*;
import fortress.tfol.*;
import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;

public class FreeVarsTest {
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    Var c = Term.mkVar("c");
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    
    Term t1 = Term.mkAnd(
        Term.mkApp("R", x),
        Term.mkNot(
            Term.mkImp(
                Term.mkApp("Q", y),
                Term.mkApp("R", x)
            )
        )
    );
    
    @Test
    public void simpleTerm() {
        assertEquals(Set.of(x, y), t1.freeVarConstSymbolsJava());
        assertEquals(Set.of(x, y), t1.freeVars(Signature.empty()));
    }
    
    @Test
    public void quantifiedTerm() {
        Term t2 = Term.mkForall(List.of(x.of(A), y.of(B)), Term.mkImp(t1, z));
        assertEquals(Set.of(z), t2.freeVarConstSymbolsJava());
        assertEquals(Set.of(z), t2.freeVars(Signature.empty()));
    }
    
    @Test
    public void constantsNotFree() {
        Signature sig = Signature.empty()
            .withType(A)
            .withConstant(c.of(A))
            .withConstant(p.of(Type.Bool()));
            
        Term t = Term.mkAnd(
            Term.mkEq(c, x),
            Term.mkImp(p, q)
        );
        
        assertEquals(Set.of(x, q), t.freeVars(sig));
    }
}
