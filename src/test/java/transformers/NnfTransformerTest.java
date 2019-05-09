import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.transformers.*;
import java.util.List;

public class NnfTransformerTest {
    
    TheoryTransformer nnf = new NnfTransformer();
    
    Sort A = Sort.mkSortConst("A");
    Sort B = Sort.mkSortConst("B");
    
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, A);
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Sort.Bool());
    
    Theory baseTheory = Theory.empty()
        .withSort(A)
        .withSort(B)
        .withConstant(p.of(Sort.Bool()))
        .withConstant(q.of(Sort.Bool()))
        .withFunctionDeclaration(f)
        .withFunctionDeclaration(P);
    
    @Test
    public void simpleAndTheory() {
        Theory theory = baseTheory
            .withAxiom(Term.mkNot(Term.mkAnd(p, Term.mkNot(p))));
        
        Theory expected = baseTheory
            .withAxiom(Term.mkOr(Term.mkNot(p), p));
        
        assertEquals(expected, nnf.apply(theory));
    }
    
    @Test
    public void nnfImp() {
        Theory theory = baseTheory
            .withAxiom(Term.mkImp(p, q));
            
        Theory expected = baseTheory
            .withAxiom(Term.mkOr(Term.mkNot(p), q));

        assertEquals(expected, nnf.apply(theory));
    }

    @Test
    public void nnfIff() {
        Theory theory = baseTheory
            .withAxiom(Term.mkEq(p, q));
            
        Theory expected = baseTheory
            .withAxiom(Term.mkOr(Term.mkAnd(p, q),
                                 Term.mkAnd(Term.mkNot(p), Term.mkNot(q))));

        assertEquals(expected, nnf.apply(theory));
    }

    @Test
    public void nnfNotAnd() {
        Theory theory = baseTheory
            .withAxiom(Term.mkNot(Term.mkAnd(p, q)));
            
        Theory expected = baseTheory
            .withAxiom(Term.mkOr(Term.mkNot(p), Term.mkNot(q)));

        assertEquals(expected, nnf.apply(theory));
    }
    
    @Test
    public void nnfNotOr() {
        Theory theory = baseTheory
            .withAxiom(Term.mkNot(Term.mkOr(p, q)));
            
        Theory expected = baseTheory
            .withAxiom(Term.mkAnd(Term.mkNot(p), Term.mkNot(q)));

        assertEquals(expected, nnf.apply(theory));
    }

    @Test
    public void nnfNotNot() {
        Theory theory = baseTheory
            .withAxiom(Term.mkNot(Term.mkNot(p)));
            
        Theory expected = baseTheory
            .withAxiom(p);

        assertEquals(expected, nnf.apply(theory));
    }

    @Test
    public void nnfNotExists() {
        Theory theory = baseTheory
            .withAxiom(Term.mkNot(Term.mkExists(x.of(A), Term.mkApp("P", x))));
            
        Theory expected = baseTheory
            .withAxiom(Term.mkForall(x.of(A), Term.mkNot(Term.mkApp("P", x))));

        assertEquals(expected, nnf.apply(theory));
    }

    @Test
    public void nnfNotForall() {
        Theory theory = baseTheory
            .withAxiom(Term.mkNot(Term.mkForall(x.of(A), Term.mkApp("P", x))));
            
        Theory expected = baseTheory
            .withAxiom(Term.mkExists(x.of(A), Term.mkNot(Term.mkApp("P", x))));

        assertEquals(expected, nnf.apply(theory));
    }
    
    @Test
    public void nnfNotImp() {
        Theory theory = baseTheory
            .withAxiom(Term.mkNot(Term.mkImp(p, q)));
            
        Theory expected = baseTheory
            .withAxiom(Term.mkAnd(p, Term.mkNot(q)));

        assertEquals(expected, nnf.apply(theory));
    }

    @Test
    public void nnfNotIff() {
        Theory theory = baseTheory
            .withAxiom(Term.mkNot(Term.mkEq(p, q)));
            
        Theory expected = baseTheory
            .withAxiom(Term.mkOr(Term.mkAnd(p, Term.mkNot(q)),
                                 Term.mkAnd(Term.mkNot(p), q)));

        assertEquals(expected, nnf.apply(theory));
    }
    
    @Test
    public void complex1() {
        Term axiom = Term.mkNot(
            Term.mkExists(
                x.of(A),
                Term.mkEq(
                    Term.mkNot(p),
                    Term.mkNot(Term.mkOr(q, p)))));;
        Term expectedAxiom =
            Term.mkForall(
                x.of(A),
                Term.mkOr(
                    Term.mkAnd(Term.mkNot(p), Term.mkOr(q, p)),
                    Term.mkAnd(p, Term.mkAnd(Term.mkNot(q), Term.mkNot(p)))));
        Theory theory = baseTheory.withAxiom(axiom);
        Theory expected = baseTheory.withAxiom(expectedAxiom);
        assertEquals(expected, nnf.apply(theory));
    }
    
    @Test
    public void complex2() {
        // ~ ( exists x . (~p) <=> ~(q OR (forall x . ~(P(x) AND (~~q) => p))) )
        Term axiom = Term.mkNot(
            Term.mkExists(
                x.of(A),
                Term.mkEq(
                    Term.mkNot(p),
                    Term.mkNot(
                        Term.mkOr(
                            q,
                            Term.mkForall(
                                x.of(A),
                                Term.mkNot(
                                    Term.mkAnd(
                                        Term.mkApp("P", x),
                                        Term.mkImp(
                                            Term.mkNot(Term.mkNot(q)),
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
        // forall x. (~p AND (q OR (forall x . ~P(x) OR (q AND ~p))))
        //        OR (p AND (~q AND exists x . P(x) AND (~q OR p)))
        Term expectedAxiom =
            Term.mkForall(
                x.of(A),
                Term.mkOr(
                    Term.mkAnd(
                        Term.mkNot(p),
                        Term.mkOr(
                            q,
                            Term.mkForall(
                                x.of(A),
                                Term.mkOr(
                                    Term.mkNot(Term.mkApp("P", x)),
                                    Term.mkAnd(
                                        q,
                                        Term.mkNot(p)
                                    )
                                )
                            )
                        )
                    ),
                    Term.mkAnd(
                        p,
                        Term.mkAnd(
                            Term.mkNot(q),
                            Term.mkExists(
                                x.of(A),
                                Term.mkAnd(
                                    Term.mkApp("P", x),
                                    Term.mkOr(
                                        Term.mkNot(q),
                                        p
                                    )
                                )
                            )
                        )
                    )
                )
            );
        Theory theory = baseTheory
            .withAxiom(axiom);
            
        Theory expected = baseTheory
            .withAxiom(expectedAxiom);
        
        assertEquals(expected, nnf.apply(theory));
    }
    
    @Test // Former bug
    public void distinct() {
        Sort U = Sort.mkSortConst("U");
        Var x = Term.mkVar("x");
        Var y = Term.mkVar("y");
        Var z = Term.mkVar("z");
        FuncDecl P = FuncDecl.mkFuncDecl("P", U, U, U, Sort.Bool());
        
        Term t = Term.mkForall(List.of(x.of(U), y.of(U), z.of(U)),
            Term.mkImp(Term.mkApp("P", x, y, z), Term.mkDistinct(x, y, z)));
        
        Term e = Term.mkForall(List.of(x.of(U), y.of(U), z.of(U)),
            Term.mkOr(
                Term.mkNot(Term.mkApp("P", x, y, z)),
                Term.mkAnd(
                    Term.mkNot(Term.mkEq(x, y)),
                    Term.mkNot(Term.mkEq(x, z)),
                    Term.mkNot(Term.mkEq(y, z)))));
                    
        Theory base = Theory.empty()
            .withSort(U)
            .withFunctionDeclaration(P);
        Theory theory = base.withAxiom(t);
        Theory expected = base.withAxiom(e);
        
        assertEquals(expected, nnf.apply(theory));
    }
    
    @Test // Former bug
    public void distinct2() {
        Sort V = Sort.mkSortConst("V");
        FuncDecl adj = FuncDecl.mkFuncDecl("adj", V, V, Sort.Bool());
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Var x3 = Term.mkVar("x3");
        
        Term t1 = Term.mkForall(List.of(x1.of(V), x2.of(V), x3.of(V)),
            Term.mkImp(
                Term.mkDistinct(x1, x2, x3),
                Term.mkNot(Term.mkEq(
                    Term.mkApp("adj", x1, x2),
                    Term.mkApp("adj", x2, x3)))));
                    
        Term t2 = Term.mkForall(List.of(x1.of(V), x2.of(V), x3.of(V)),
            Term.mkImp(
                Term.mkAnd(
                    Term.mkNot(Term.mkEq(x1, x2)),
                    Term.mkNot(Term.mkEq(x1, x3)),
                    Term.mkNot(Term.mkEq(x2, x3))),
                Term.mkNot(Term.mkEq(
                    Term.mkApp("adj", x1, x2),
                    Term.mkApp("adj", x2, x3)))));
        
        Theory base = Theory.empty()
            .withSort(V)
            .withFunctionDeclaration(adj);
        
        Theory theory1 = base.withAxiom(t1);
        Theory theory2 = base.withAxiom(t2);
        
        assertEquals(nnf.apply(theory2), nnf.apply(theory1));
    }
    
    @Test
    public void distinct3() {
        Sort V = Sort.mkSortConst("V");
        FuncDecl adj = FuncDecl.mkFuncDecl("adj", V, V, Sort.Bool());
        Var x1 = Term.mkVar("x1");
        Var x2 = Term.mkVar("x2");
        Var x3 = Term.mkVar("x3");
        
        Term t1 = Term.mkNot(Term.mkExists(List.of(x1.of(V), x2.of(V), x3.of(V)),
            Term.mkAnd(
                Term.mkDistinct(x1, x2, x3),
                (Term.mkEq(
                    Term.mkApp("adj", x1, x2),
                    Term.mkApp("adj", x2, x3))))));
                    
        Term t2 = Term.mkForall(List.of(x1.of(V), x2.of(V), x3.of(V)),
            Term.mkImp(
                Term.mkAnd(
                    Term.mkNot(Term.mkEq(x1, x2)),
                    Term.mkNot(Term.mkEq(x1, x3)),
                    Term.mkNot(Term.mkEq(x2, x3))),
                Term.mkNot(Term.mkEq(
                    Term.mkApp("adj", x1, x2),
                    Term.mkApp("adj", x2, x3)))));
        
        Theory base = Theory.empty()
            .withSort(V)
            .withFunctionDeclaration(adj);
        
        Theory theory1 = base.withAxiom(t1);
        Theory theory2 = base.withAxiom(t2);
        
        assertEquals(nnf.apply(theory2), nnf.apply(theory1));
    }
}
