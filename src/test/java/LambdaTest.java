import static org.junit.Assert.assertEquals;
import org.junit.Test;

import fortress.lambda.*;
import fortress.fol.pterm.*;

import java.util.*;
import java.util.Arrays.*;

public class LambdaTest {
    
    @Test
    public void freeVars() {
        PTerm typeA = new PVar("A");
        PTerm typeAA = Type.mkFnTy(typeA, typeA);
        PTerm typeAA_A = Type.mkFnTy(typeAA, typeA);
        Var x = new Var("x", typeAA);
        Var y = new Var("y", typeA);
        Var z = new Var("z", Type.mkFnTy(typeAA_A, typeA));
        
        Set<Var> expect = new HashSet<Var>();
        expect.add(x);
        assertEquals(expect, x.fv());
        
        Term t1 = new App(x, y);
        expect = new HashSet<Var>();
        expect.add(x);
        expect.add(y);
        assertEquals(expect, t1.fv());

        Term t2 = new Abs(x, t1);
        expect = new HashSet<Var>();
        expect.add(y);
        assertEquals(expect, t2.fv());

        Term t3 = new App(z, t2);
        expect = new HashSet<Var>();
        expect.add(z);
        expect.add(y);
        assertEquals(expect, t3.fv());
    }
}
