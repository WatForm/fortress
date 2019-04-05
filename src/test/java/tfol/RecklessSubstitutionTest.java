import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.tfol.*;
import java.util.List;
import java.util.Set;
import java.util.Map;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;

public class RecklessSubstitutionTest {
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    
    Var w = Term.mkVar("w");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    Var z = Term.mkVar("z");
    Var a = Term.mkVar("a");
    Var b = Term.mkVar("b");
    Var c = Term.mkVar("c");
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    
    Var _1 = Term.mkVar("_1");
    Var _2 = Term.mkVar("_2");
    
    @Test
    public void basicSubstitution() {
        Term t = Term.mkImp(p, Term.mkEq(x, Term.mkApp("f", y)));
        Term expected = Term.mkImp(p, Term.mkEq(Term.mkApp("h", z), Term.mkApp("f", y)));
        assertEquals(expected, t.recklessSubstitute(Map.of(x, Term.mkApp("h", z))));
    }
    
    @Test
    public void boundVar() {
        Term t1 = Term.mkAnd(Term.mkEq(x, x),
                       Term.mkExists(x.of(A), Term.mkApp("R", x)));
                       
        Term t2 = Term.mkAnd(Term.mkEq(x, x),
                       Term.mkForall(x.of(A), Term.mkApp("R", x)));
                       
        Term e1 = Term.mkAnd(Term.mkEq(Term.mkBottom(), Term.mkBottom()),
                      Term.mkExists(x.of(A), Term.mkApp("R", x)));
                      
        Term e2 = Term.mkAnd(Term.mkEq(Term.mkBottom(), Term.mkBottom()),
                      Term.mkForall(x.of(A), Term.mkApp("R", x)));
                      
        assertEquals(e1, t1.recklessSubstitute(Map.of(x, Term.mkBottom())));
        assertEquals(e2, t2.recklessSubstitute(Map.of(x, Term.mkBottom())));
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void basicSubstitutionMultiple1() {
        
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void basicSubstitutionMultiple2() {
        
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void boundVarMultiple1() {
        
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void boundVarMultiple2() {
        
    }
    
}
