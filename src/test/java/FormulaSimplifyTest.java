import org.junit.Test;
import org.junit.Ignore;
import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import fortress.lambda.*;
import fortress.fol.pterm.*;
import fortress.fol.*;
import fortress.Constants;

import java.util.*;
import java.util.Arrays.*;

public class FormulaSimplifyTest {
    // Note that Formula.fromTerm performs some simplification
    // so be careful using it in testing

    @Test
    public void simplifyMultipleNeg() {
        Term t = FOL.mkNot(FOL.mkNot(FOL.mkNot(FOL.mkProp("p"))));
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(FOL.mkNot(FOL.mkProp("p")));
        assertThat(f, not(expected));
        assertEquals(expected, f.simplify());
    }

    @Test
    public void simplifyNotTrueFalse() {
        Term t1 = FOL.mkNot(FOL.mkNot(FOL.mkNot(FOL.true_)));
        Term t2 = FOL.mkNot(FOL.mkNot(FOL.mkNot(FOL.false_)));
        Formula f1 = Formula.fromTerm(t1);
        Formula f2 = Formula.fromTerm(t2);
        Formula expected1 = Formula.fromTerm(FOL.false_);
        Formula expected2 = Formula.fromTerm(FOL.true_);
        assertThat(f1, not(expected1));
        assertThat(f2, not(expected2));
        assertEquals(expected1, f1.simplify());
        assertEquals(expected2, f2.simplify());
    }

    @Test
    public void simplifyOrFlatten() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula q = Formula.fromTerm(FOL.mkProp("q"));
        Formula r = Formula.fromTerm(FOL.mkProp("r"));
        Formula s = Formula.fromTerm(FOL.mkProp("s"));
        Formula f = new Or(
            p,
            new Or(
                q,
                new Or(
                    r,
                    s
                )
            )
        );
        Formula expected = new Or(p, q, r, s);
        assertThat(f, not(expected));
        assertEquals(expected, f.simplify());
    }

    @Test
    public void simplifyOrTrueFalse() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula q = Formula.fromTerm(FOL.mkProp("q"));
        Formula r = Formula.fromTerm(FOL.mkProp("r"));
        Formula tru = Formula.fromTerm(FOL.true_);
        Formula fls = Formula.fromTerm(FOL.false_);

        Formula f1  = new Or(
            p,
            fls,
            new Or(
                q,
                new Or(
                    fls,
                    r
                )
            )
        );
        Formula expected1 = new Or(p, q, r);
        assertThat(f1, not(expected1));
        assertEquals(expected1, f1.simplify());

        Formula f2 = new Or(
            p,
            fls,
            new Or(
                q,
                new Or(
                    tru,
                    r
                )
            )
        );
        Formula expected2 = tru;
        assertThat(f2, not(expected2));
        assertEquals(expected2, f2.simplify());
    }

    @Test
    public void simplifyOrSingleton() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula fls = Formula.fromTerm(FOL.false_);

        SortedSet<Formula> formulas = new TreeSet<>();
        formulas.add(p);
        Formula f1 = new Or(formulas);
        assertThat(f1, not(p));
        assertEquals(p, f1.simplify());

        Formula f2 = new Or(
            p,
            fls,
            new Or(
                p,
                new Or(
                    fls,
                    p
                )
            )
        );
        assertThat(f2, not(p));
        assertEquals(p, f2.simplify());
    }

    @Test
    public void simplifyOrLawExcludedMiddle() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula tru = Formula.fromTerm(FOL.true_);
        Formula f = new Or(p, new Not(p));
        assertThat(f, not(tru));
        assertEquals(tru, f.simplify());
    }

    @Test
    public void simplifyAndFlatten() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula q = Formula.fromTerm(FOL.mkProp("q"));
        Formula r = Formula.fromTerm(FOL.mkProp("r"));
        Formula s = Formula.fromTerm(FOL.mkProp("s"));
        Formula f = new And(
            p,
            new And(
                q,
                new And(
                    r,
                    s
                )
            )
        );
        Formula expected = new And(p, q, r, s);
        assertThat(f, not(expected));
        assertEquals(expected, f.simplify());
    }

    @Test
    public void simplifyAndTrueFalse() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula q = Formula.fromTerm(FOL.mkProp("q"));
        Formula r = Formula.fromTerm(FOL.mkProp("r"));
        Formula tru = Formula.fromTerm(FOL.true_);
        Formula fls = Formula.fromTerm(FOL.false_);

        Formula f1  = new And(
            p,
            tru,
            new And(
                q,
                new And(
                    tru,
                    r
                )
            )
        );
        Formula expected1 = new And(p, q, r);
        assertThat(f1, not(expected1));
        assertEquals(expected1, f1.simplify());

        Formula f2 = new And(
            p,
            tru,
            new And(
                q,
                new And(
                    fls,
                    r
                )
            )
        );
        Formula expected2 = fls;
        assertThat(f2, not(expected2));
        assertEquals(expected2, f2.simplify());
    }

    @Test
    public void simplifyAndSingleton() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula tru = Formula.fromTerm(FOL.true_);

        SortedSet<Formula> formulas = new TreeSet<>();
        formulas.add(p);
        Formula f1 = new And(formulas);
        assertThat(f1, not(p));
        assertEquals(p, f1.simplify());

        Formula f2 = new And(
            p,
            tru,
            new And(
                p,
                new And(
                    tru,
                    p
                )
            )
        );
        assertThat(f2, not(p));
        assertEquals(p, f2.simplify());
    }

    @Test
    public void simplifyAndContradiction() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula fls = Formula.fromTerm(FOL.false_);
        Formula f = new And(p, new Not(p));
        assertThat(f, not(fls));
        assertEquals(fls, f.simplify());
    }

    @Test
    public void simplifyImpTrueFalse() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula tru = Formula.fromTerm(FOL.true_);
        Formula fls = Formula.fromTerm(FOL.false_);

        Formula f1 = new Imp(fls, p);
        assertThat(f1, not(tru));
        assertEquals(tru, f1.simplify());

        Formula f2 = new Imp(p, tru);
        assertThat(f2, not(tru));
        assertEquals(tru, f2.simplify());

        Formula f3 = new Imp(tru, p);
        assertThat(f3, not(p));
        assertEquals(p, f3.simplify());

        Formula f4 = new Imp(p, fls);
        assertThat(f4, not(new Not(p)));
        assertEquals(new Not(p), f4.simplify());
    }

    @Test
    public void simplifyImpSelf() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula tru = Formula.fromTerm(FOL.true_);
        Formula f = new Imp(p, p);
        assertThat(p, not(tru));
        assertEquals(tru, f.simplify());
    }

    @Test
    public void simplifyImpNotSelf() {
        // p implies (not p)
        // If (not p) is true, then anything, including p, implies (not p)
        // If p implies (not p), this is a proof by contradiction for (not p)
        // So p implies (not p) is equivalent to (not p)
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula f = new Imp(p, new Not(p));
        assertThat(f, not(new Not(p)));
        assertEquals(new Not(p), f.simplify());
    }

    @Test
    public void simplifyIffTrueFalse() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula tru = Formula.fromTerm(FOL.true_);
        Formula fls = Formula.fromTerm(FOL.false_);

        Formula f1 = new Iff(tru, p);
        Formula f2 = new Iff(p, tru);
        assertThat(f1, not(p));
        assertThat(f2, not(p));
        assertEquals(p, f1.simplify());
        assertEquals(p, f2.simplify());

        Formula f3 = new Iff(p, fls);
        Formula f4 = new Iff(fls, p);
        assertThat(f3, not(new Not(p)));
        assertThat(f4, not(new Not(p)));
        assertEquals(new Not(p), f3.simplify());
        assertEquals(new Not(p), f4.simplify());
    }

    @Test
    public void simplifyIffSelf() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula tru = Formula.fromTerm(FOL.true_);
        Formula f = new Iff(p, p);
        assertThat(f, not(tru));
        assertEquals(tru, f.simplify());
    }

    @Test
    public void simplifyIffNotSelf() {
        Formula p = Formula.fromTerm(FOL.mkProp("p"));
        Formula fls = Formula.fromTerm(FOL.false_);
        Formula f = new Iff(p, new Not(p));
        assertThat(f, not(fls));
        assertEquals(fls, f.simplify());
    }

    @Test
    @Ignore ("Test not implemented")
    public void simplifyForallFlatten() {
        
    }

    @Test
    @Ignore ("Test not implemented")
    public void simplifyForallTrueFalse() {
        
    }

    @Test
    @Ignore ("Test not implemented")
    public void simplifyExistsFlatten() {
        
    }

    @Test
    @Ignore ("Test not implemented")
    public void simplifyExistsTrueFalse() {
        
    }

    @Test
    @Ignore ("Test not implemented")
    public void simplifyComplex1() {
        
    }

    @Test
    @Ignore ("Test not implemented")
    public void simplifyComplex2() {
        
    }
}
