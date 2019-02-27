import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;

public class DeBruijnTest {
    
    Type A = Type.mkTypeConst("A");
    
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    Var a = Term.mkVar("a");
    Var b = Term.mkVar("b");
    Var c = Term.mkVar("c");
    
    Var _1 = Term.mkVar("_1");
    Var _2 = Term.mkVar("_2");
    Var _3 = Term.mkVar("_3");
    Var _4 = Term.mkVar("_4");
    Var _5 = Term.mkVar("_5");
    Var _6 = Term.mkVar("_6");
    
    @Test
    public void basicForallExists() {
        Term t1 = Term.mkForall(x.of(A), Term.mkApp("p", x));
        Term t2 = Term.mkExists(x.of(A), Term.mkApp("p", x));
        
        Term e1 = Term.mkForall(_1.of(A), Term.mkApp("p", _1));
        Term e2 = Term.mkExists(_1.of(A), Term.mkApp("p", _1));
        
        assertEquals(e1, t1.deBruijn());
        assertEquals(e2, t2.deBruijn());
    }
    
    @Test
    public void nestedForallExists() {
        Term t = Term.mkForall(x.of(A), Term.mkExists(y.of(A), Term.mkAnd(Term.mkApp("p", x), Term.mkApp("p", y))));
        Term e = Term.mkForall(_1.of(A), Term.mkExists(_2.of(A), Term.mkAnd(Term.mkApp("p", _1), Term.mkApp("p", _2))));
        assertEquals(e, t.deBruijn());
    }
    
    @Test
    public void freeVarsLeftAlone() {
        Term t = Term.mkForall(x.of(A), Term.mkExists(y.of(A), Term.mkAnd(Term.mkApp("p", z), Term.mkApp("p", y))));
        Term e = Term.mkForall(_1.of(A), Term.mkExists(_2.of(A), Term.mkAnd(Term.mkApp("p", z), Term.mkApp("p", _2))));
        assertEquals(e, t.deBruijn());
    }
    
    @Test
    public void branching() {
        Term t = Term.mkForall(x.of(A),
            Term.mkAnd(
                Term.mkExists(y.of(A), Term.mkAnd(Term.mkApp("p", x), Term.mkApp("p", y))),
                Term.mkExists(z.of(A), Term.mkAnd(Term.mkApp("p", x), Term.mkApp("p", z)))
            ));
        Term e = Term.mkForall(_1.of(A),
            Term.mkAnd(
                Term.mkExists(_2.of(A), Term.mkAnd(Term.mkApp("p", _1), Term.mkApp("p", _2))),
                Term.mkExists(_2.of(A), Term.mkAnd(Term.mkApp("p", _1), Term.mkApp("p", _2)))
            ));
        assertEquals(e, t.deBruijn());
    }
    
    @Test
    public void shadow() {
        Term t1 = Term.mkForall(x.of(A), Term.mkExists(x.of(A), Term.mkApp("p", x)));
        Term t2 = Term.mkExists(x.of(A), Term.mkForall(x.of(A), Term.mkApp("p", x)));
        Term e1 = Term.mkForall(_1.of(A), Term.mkExists(_2.of(A), Term.mkApp("p", _2)));
        Term e2 = Term.mkExists(_1.of(A), Term.mkForall(_2.of(A), Term.mkApp("p", _2)));
        assertEquals(e1, t1.deBruijn());
        assertEquals(e2, t2.deBruijn());
    }
    
    // TODO: need more tests in other areas that check quantifiers with multiple variables
    
    @Test
    public void multivarQuantifier() {
        Term t1 = Term.mkForall(List.of(x.of(A), y.of(A), z.of(A)), Term.mkAnd(
            Term.mkApp("p", x), Term.mkApp("p", z), Term.mkApp("p", y)
        ));
        Term t2 = Term.mkExists(List.of(x.of(A), y.of(A), z.of(A)), Term.mkAnd(
            Term.mkApp("p", x), Term.mkApp("p", z), Term.mkApp("p", y)
        ));
        Term e1 = Term.mkForall(List.of(_1.of(A), _2.of(A), _3.of(A)), Term.mkAnd(
            Term.mkApp("p", _1), Term.mkApp("p", _3), Term.mkApp("p", _2)
        ));
        Term e2 = Term.mkExists(List.of(_1.of(A), _2.of(A), _3.of(A)), Term.mkAnd(
            Term.mkApp("p", _1), Term.mkApp("p", _3), Term.mkApp("p", _2)
        ));
        assertEquals(e1, t1.deBruijn());
        assertEquals(e2, t2.deBruijn());
    }
    
    @Test
    public void multivarQuantifierBranch() {
        Term t = Term.mkForall(List.of(x.of(A), y.of(A)),
            Term.mkAnd(
                Term.mkExists(List.of(x.of(A), y.of(A), z.of(A)),
                    Term.mkAnd(Term.mkApp("p", x), Term.mkApp("p", y), Term.mkApp("p", z))),
                Term.mkExists(List.of(y.of(A), z.of(A), x.of(A)),
                    Term.mkAnd(Term.mkApp("p", x), Term.mkApp("p", y), Term.mkApp("p", z)))
            ));
        Term e = Term.mkForall(List.of(_1.of(A), _2.of(A)),
            Term.mkAnd(
                Term.mkExists(List.of(_3.of(A), _4.of(A), _5.of(A)),
                    Term.mkAnd(Term.mkApp("p", _3), Term.mkApp("p", _4), Term.mkApp("p", _5))),
                Term.mkExists(List.of(_3.of(A), _4.of(A), _5.of(A)),
                    Term.mkAnd(Term.mkApp("p", _5), Term.mkApp("p", _3), Term.mkApp("p", _4)))
            ));
        assertEquals(e, t.deBruijn());
    }
}
