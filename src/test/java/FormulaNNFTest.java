import static org.junit.Assert.assertEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.lambda.*;
import fortress.fol.pterm.*;
import fortress.fol.*;
import fortress.Constants;

import java.util.*;
import java.util.Arrays.*;

public class FormulaNNFTest {

    @Test
    @Ignore ("Test not implemented")
    public void nnfTrue() {
        
    }

    @Test
    @Ignore ("Test not implemented")
    public void nnfFalse() {
        
    }

    @Test
    public void nnfImp() {
        Term t = FOL.mkImp(
            FOL.mkProp("p"),
            FOL.mkProp("q")
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkOr(
                FOL.mkNot(FOL.mkProp("p")),
                FOL.mkProp("q")
            )
        );
        assertEquals(expected, f.nnf());
    }

    @Test
    public void nnfIff() {
        Term t = FOL.mkIff(
            FOL.mkProp("p"),
            FOL.mkProp("q")
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkOr(
                FOL.mkAnd(FOL.mkProp("p"), FOL.mkProp("q")),
                FOL.mkAnd(FOL.mkNot(FOL.mkProp("p")), FOL.mkNot(FOL.mkProp("q")))
            )
        );
        assertEquals(expected, f.nnf());
    }

    @Test
    public void nnfNotAnd() {
        Term t = FOL.mkNot(
            FOL.mkAnd(
                FOL.mkProp("p"),
                FOL.mkProp("q")
            )
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkOr(
                FOL.mkNot(FOL.mkProp("p")),
                FOL.mkNot(FOL.mkProp("q"))
            )
        );
        assertEquals(expected, f.nnf());
    }
    
    @Test
    public void nnfNotOr() {
        Term t = FOL.mkNot(
            FOL.mkOr(
                FOL.mkProp("p"),
                FOL.mkProp("q")
            )
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkAnd(
                FOL.mkNot(FOL.mkProp("p")),
                FOL.mkNot(FOL.mkProp("q"))
            )
        );
        assertEquals(expected, f.nnf());
    }

    @Test
    public void nnfNotNot() {
        Term t = FOL.mkNot(FOL.mkNot(FOL.mkProp("p")));
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(FOL.mkProp("p"));
        assertEquals(expected, f.nnf());
    }

    @Test
    public void nnfNotExists() {
        PVar a = new PVar("a");
        Const p = FOL.mkFun("p", a, Type.BOOL); 
        Var x = new Var("x", a);
        Term t = FOL.mkNot(
            FOL.mkExists(
                x,
                FOL.apply(p, x)
            )
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkForall(
                x,
                FOL.mkNot(FOL.apply(p, x))
            )
        );
        assertEquals(expected, f.nnf());
    }

    @Test
    public void nnfNotForall() {
        PVar a = new PVar("a");
        Const p = FOL.mkFun("p", a, Type.BOOL);
        Var x = new Var("x", a);
        Term t = FOL.mkNot(
            FOL.mkForall(
                x,
                FOL.apply(p, x)
            )
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkExists(
                x,
                FOL.mkNot(FOL.apply(p, x))
            )
        );
        assertEquals(expected, f.nnf());
    }
    
    @Test
    public void nnfNotImp() {
        Term t = FOL.mkNot(
            FOL.mkImp(
                FOL.mkProp("p"),
                FOL.mkProp("q")
            )
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkAnd(
                FOL.mkProp("p"),
                FOL.mkNot(FOL.mkProp("q"))
            )
        );
        assertEquals(expected, f.nnf());
    }

    @Test
    public void nnfNotIff() {
        Term t = FOL.mkNot(
            FOL.mkIff(
                FOL.mkProp("p"),
                FOL.mkProp("q")
            )
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkOr(
                FOL.mkAnd(FOL.mkProp("p"), FOL.mkNot(FOL.mkProp("q"))),
                FOL.mkAnd(FOL.mkNot(FOL.mkProp("p")), FOL.mkProp("q"))
            )
        );
        assertEquals(expected, f.nnf());
    }

    @Test
    public void nnfComplex1() {
        PVar a = new PVar("a");
        Term p = FOL.mkProp("p");
        Term q = FOL.mkProp("q");
        Var x = new Var("x", a);
        Const h = FOL.mkFun("h", a, Type.BOOL);
        Term t = FOL.mkNot(
            FOL.mkExists(
                x,
                FOL.mkIff(
                    FOL.mkNot(p),
                    FOL.mkNot(
                        FOL.mkOr(
                            q,
                            FOL.mkForall(
                                x,
                                FOL.mkNot(
                                    FOL.mkAnd(
                                        FOL.apply(h, x),
                                        FOL.mkImp(
                                            FOL.mkNot(FOL.mkNot(q)),
                                            p
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkForall(
                x,
                FOL.mkOr(
                    FOL.mkAnd(
                        p,
                        FOL.mkAnd(
                            FOL.mkNot(q),
                            FOL.mkExists(
                                x,
                                FOL.mkAnd(
                                    FOL.apply(h, x),
                                    FOL.mkOr(
                                        FOL.mkNot(q),
                                        p
                                    )
                                )
                            )
                        )
                    ),
                    FOL.mkAnd(
                        FOL.mkNot(p),
                        FOL.mkOr(
                            q,
                            FOL.mkForall(
                                x,
                                FOL.mkOr(
                                    FOL.mkNot(FOL.apply(h, x)),
                                    FOL.mkAnd(
                                        q,
                                        FOL.mkNot(p)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );
        assertEquals(expected, f.nnf());
    }
    
    @Test
    public void nnfComplex2() {
        // Modification of "complex" test, which failed due to a bug
        // about creating formulas with quantifiers
        PVar a = new PVar("a");
        Term p = FOL.mkProp("p");
        Term q = FOL.mkProp("q");
        Var x = new Var("x", a);
        Var y = new Var("y", a);
        Const h = FOL.mkFun("h", a, Type.BOOL);
        Term t = FOL.mkNot(
            FOL.mkExists(
                x,
                FOL.mkIff(
                    FOL.mkNot(FOL.apply(h, x)),
                    FOL.mkNot(
                        FOL.mkOr(
                            q,
                            FOL.mkForall(
                                y,
                                FOL.mkNot(
                                    FOL.mkAnd(
                                        FOL.apply(h, y),
                                        FOL.mkImp(
                                            FOL.mkNot(FOL.mkNot(q)),
                                            p
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );
        Formula f = Formula.fromTerm(t);
        Formula expected = Formula.fromTerm(
            FOL.mkForall(
                x,
                FOL.mkOr(
                    FOL.mkAnd(
                        FOL.apply(h, x),
                        FOL.mkAnd(
                            FOL.mkNot(q),
                            FOL.mkExists(
                                y,
                                FOL.mkAnd(
                                    FOL.apply(h, y),
                                    FOL.mkOr(
                                        FOL.mkNot(q),
                                        p
                                    )
                                )
                            )
                        )
                    ),
                    FOL.mkAnd(
                        FOL.mkNot(FOL.apply(h, x)),
                        FOL.mkOr(
                            q,
                            FOL.mkForall(
                                y,
                                FOL.mkOr(
                                    FOL.mkNot(FOL.apply(h, y)),
                                    FOL.mkAnd(
                                        q,
                                        FOL.mkNot(p)
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );
        assertEquals(expected.simplify(), f.nnf().simplify());
    }
    
    
    
}
