import static org.junit.Assert.*;
import org.junit.Test;
import org.junit.Before;

import fortress.lambda.*;
import fortress.fol.pterm.*;
import fortress.Constants;
import fortress.util.Pair;

import java.util.*;
import java.util.Arrays.*;
import java.lang.AssertionError;

public class PTermUnifyTest {

    PVar a = new PVar("A");
    PVar b = new PVar("B");
    PVar c = new PVar("C");
    PVar d = new PVar("D");

    PTerm funAB = new Com(Constants.FN_Str, Arrays.asList(a, b));
    PTerm funBA = new Com(Constants.FN_Str, Arrays.asList(b, a));
    PTerm funCD = new Com(Constants.FN_Str, Arrays.asList(c, d));
    PTerm funBC = new Com(Constants.FN_Str, Arrays.asList(b, c));
    PTerm funABC = new Com(Constants.FN_Str, Arrays.asList(a, funBC));

    List<Pair<PTerm, PTerm>> eqs;
    Map<PVar, PTerm> sigma;

    @Before
    public void setup() {
        eqs = new ArrayList<>();
        sigma = new HashMap<>();
    }

    @Test
    public void unifyWithSelf() {
        eqs.add(new Pair(a, a));
        eqs.add(new Pair(funAB, funAB));
        sigma = PTerm.unify(eqs);
        assertEquals(sigma, new HashMap<PVar, PTerm>());
    }

    @Test
    public void unifySimple() {
        eqs.add(new Pair(a, funCD));
        sigma = PTerm.unify(eqs);
        assertEquals(a.substitute(sigma), funCD.substitute(sigma));
    }

    @Test
    public void unifyFunction() {
        assertEquals(eqs, new ArrayList<>());
        eqs.add(new Pair(funAB, funCD));
        sigma = PTerm.unify(eqs);
        assertEquals(funAB.substitute(sigma), funCD.substitute(sigma));
    }

    @Test
    public void unifyPairwise() {
        eqs.add(new Pair(a, b));
        eqs.add(new Pair(b, a));
        sigma = PTerm.unify(eqs);
        assertEquals(a.substitute(sigma), b.substitute(sigma));
    }
    
    @Test
    public void unifyRedundant() {
        eqs.add(new Pair(a, b));
        eqs.add(new Pair(a, b));
        sigma = PTerm.unify(eqs);
        assertEquals(a.substitute(sigma), b.substitute(sigma));
    }

    @Test (expected = java.lang.AssertionError.class)
    public void unifyOccurs() {
        eqs.add(new Pair(a, funAB));
        sigma = PTerm.unify(eqs);
    }

    @Test (expected = java.lang.AssertionError.class)
    public void unifyMismatch() {
        eqs.add(new Pair (funAB, funABC));
        sigma = PTerm.unify(eqs);
    }
    
}
