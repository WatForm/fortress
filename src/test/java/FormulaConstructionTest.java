import static org.junit.Assert.*;
import org.junit.Test;

import fortress.lambda.*;
import fortress.fol.pterm.*;
import fortress.fol.*;
import fortress.Constants;

import java.util.*;
import java.util.Arrays.*;

public class FormulaConstructionTest {

    @Test
    public void existsNoOccurences() {
        PVar a = new PVar("a");
        Term p = FOL.mkProp("p");
        Var x = new Var("x", a);
        Const h = FOL.mkFun("h", a, Type.BOOL);
        Const c = new Const("c", a);
        
        Term t1 = FOL.mkExists(x, FOL.true_);
        assertTrue(FOL.isExists(t1));
        Formula f1 = Formula.fromTerm(t1);
        assertEquals(f1, f1);
        
        Term t2 = FOL.mkExists(x, p);
        assertTrue(FOL.isExists(t2));
        Formula f2 = Formula.fromTerm(t2);
        assertEquals(f2, f2);
        
        Term t3 = FOL.mkExists(x, FOL.apply(h, c));
        assertTrue(FOL.isExists(t3));
        Formula f3 = Formula.fromTerm(t3);
        assertEquals(f3, f3);
    }

    @Test
    public void existsOtherOccurences() {
        PVar a = new PVar("a");
        Term p = FOL.mkProp("p");
        Var x = new Var("x", a);
        Var y = new Var("y", a);
        Const h = FOL.mkFun("h", a, Type.BOOL);
        
        Term t1 = FOL.mkExists(x, FOL.apply(h, y));
        assertTrue(FOL.isExists(t1));
        Formula f1 = Formula.fromTerm(t1);
        assertEquals(f1, f1);
    }
    
    @Test
    public void existsOccurence() {
        PVar a = new PVar("a");
        Term p = FOL.mkProp("p");
        Term q = FOL.mkProp("q");
        Var x = new Var("x", a);
        Const h = FOL.mkFun("h", a, Type.BOOL);
        Term t = FOL.mkExists(x, FOL.mkIff(FOL.mkNot(FOL.apply(h, x)), p));
        assertTrue(FOL.isExists(t));
        Formula f = Formula.fromTerm(t);
        assertEquals(f, f);
    }
    
    @Test
    public void existsNestedOccurence() {
        PVar a = new PVar("a");
        Term p = FOL.mkProp("p");
        Term q = FOL.mkProp("q");
        Var x = new Var("x", a);
        Const h = FOL.mkFun("h", a, Type.BOOL);
        Term t = FOL.mkExists(
            x,
            FOL.mkOr(
                FOL.apply(h, x),
                FOL.mkExists(
                    x,
                    FOL.apply(h, x)
                )
            )
        );
        assertTrue(FOL.isExists(t));
        Formula f = Formula.fromTerm(t);
        assertEquals(f, f);
    }
}
