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
    FuncDecl p = FuncDecl.mkFuncDecl("p", A, Type.Bool);
    FuncDecl q = FuncDecl.mkFuncDecl("q", B, Type. Bool);
    Var x = Term.mkVar("x", A);
    Var y = Term.mkVar("y", B);
    Var z = Term.mkVar("z", Type.Bool);
    Term t = Term.mkAnd(
        Term.mkApp(p, x),
        Term.mkNot(
            Term.mkIff(
                Term.mkApp(q, y),
                Term.mkApp(p, x)
            )
        )
    );
    
    @Test
    public void simpleTerm() {
        assertEquals(Set.of(x, y), Term.freeVariables(t));
    }
    
    @Test
    public void quantifiedTerm() {
        Term t2 = Term.mkForall(List.of(x, y), Term.mkImp(t, z));
        assertEquals(Set.of(z), Term.freeVariables(t2));
    }
}
