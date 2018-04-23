import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Before;

import fortress.lambda.*;
import fortress.fol.pterm.*;

import java.util.*;
import java.util.Arrays.*;

public class LambdaTest {

    Set<Var> expected;
    PTerm typeA = new PVar("A");
    PTerm typeAA = Type.mkFnTy(typeA, typeA);
    PTerm typeAA_A = Type.mkFnTy(typeAA, typeA);
    Var x = new Var("x", typeAA);
    Var y = new Var("y", typeA);
    Var z = new Var("z", Type.mkFnTy(typeAA_A, typeA));

    @Before
    public void setup() {
        expected = new HashSet<>();
    }
    
    @Test
    public void freeVarsVar() {
        expected.add(x);
        assertEquals(expected, x.fv());
    }

    @Test
    public void freeVarsApp() {
        Term t1 = new App(x, y);
        expected.add(x);
        expected.add(y);
        assertEquals(expected, t1.fv());
    }

    @Test
    public void freeVarsAbs() {
        Term t1 = new App(x, y);
        Term t2 = new Abs(x, t1);
        expected.add(y);
        assertEquals(expected, t2.fv());
    }

    @Test
    public void freeVarsConst() {
        Term t4 = new App(x, new Const("c", typeA));
        expected.add(x);
        assertEquals(expected, t4.fv());   
    }

    @Test
    public void freeVarsComplex1() {
        Term t1 = new App(x, y);
        Term t2 = new Abs(x, t1);
        Term t3 = new App(z, t2);
        expected.add(z);
        expected.add(y);
        assertEquals(expected, t3.fv());
    }

}
