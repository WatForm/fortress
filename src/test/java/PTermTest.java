import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Before;

import fortress.lambda.*;
import fortress.fol.pterm.*;
import fortress.Constants;

import java.util.*;
import java.util.Arrays.*;

public class PTermTest {

    Set<PVar> expected;
    PVar a = new PVar("A");
    PVar b = new PVar("B");
    PVar c = new PVar("C");
    PVar d = new PVar("D");

    @Before
    public void setup() {
        expected = new HashSet<>();
    }
    
    @Test
    public void varsSingleType() {
       expected.add(a);
       assertEquals(expected, a.vars());
   }

    @Test
    public void varsArrowType() {
        PTerm funType = new Com(Constants.FN_Str, Arrays.asList(a, b));
        expected.add(a);
        expected.add(b);
        assertEquals(expected, funType.vars());
    }

    
    @Test
    public void varsPairType() {
        PTerm funType = new Com(Constants.FN_Str, Arrays.asList(a, b));
        PTerm pairType = new Com(Constants.PAIR_Str, Arrays.asList(c, funType));
        expected = new HashSet<>();
        expected.add(a);
        expected.add(b);
        expected.add(c);
        assertEquals(expected, pairType.vars());
    }
    
    @Test
    public void substitution() {
        PTerm funType1 = new Com(Constants.FN_Str, Arrays.asList(a, b));
        PTerm pairType = new Com(Constants.PAIR_Str, Arrays.asList(b, funType1));

        PTerm funType2 = new Com(Constants.FN_Str, Arrays.asList(a, c));

        PTerm funTypeR = new Com(Constants.FN_Str, Arrays.asList(a, funType2));
        PTerm pairTypeR = new Com(Constants.PAIR_Str, Arrays.asList(funType2, funTypeR));

        assertEquals(pairTypeR, pairType.substitute(b, funType2));
        assertEquals(pairType, pairType.substitute(d, funType2));
    }
    
    @Test
    public void substitutionMap() {
        PVar a = new PVar("A");
        PVar b = new PVar("B");
        PVar c = new PVar("C");
        PVar d = new PVar("D");
        PVar e = new PVar("E");
        
        PTerm funType1 = new Com(Constants.FN_Str, Arrays.asList(a, b));
        PTerm pairType = new Com(Constants.PAIR_Str, Arrays.asList(c, funType1));
        PTerm funType2 = new Com(Constants.FN_Str, Arrays.asList(pairType, funType1));
        
        PTerm funType3 = new Com(Constants.FN_Str, Arrays.asList(d, e));
        Map<PVar, PTerm> substitution = new HashMap<>();
        substitution.put(b, funType3);
        substitution.put(c, b);
        
        PTerm funTypeR1 = new Com(Constants.FN_Str, Arrays.asList(a, funType3));
        PTerm pairTypeR = new Com(Constants.PAIR_Str, Arrays.asList(b, funTypeR1));
        PTerm funTypeR2 = new Com(Constants.FN_Str, Arrays.asList(pairTypeR, funTypeR1));
        
        assertEquals(funTypeR2, funType2.substitute(substitution));
        assertEquals(funType2, funType2.substitute(new HashMap<PVar, PTerm>()));
    }
    
    
}
