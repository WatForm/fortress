import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.transformers.*;

public class NnfTransformerTest {
    
    TheoryTransformer nnf = new NnfTransformer();
    
    Type A = Type.mkTypeConst("A");
    Type B = Type.mkTypeConst("B");
    
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    Var x = Term.mkVar("x");
    Var y = Term.mkVar("y");
    
    FuncDecl f = FuncDecl.mkFuncDecl("f", A, A);
    FuncDecl P = FuncDecl.mkFuncDecl("P", A, Type.Bool);
    
    Theory baseTheory = Theory.empty()
        .withType(A)
        .withType(B)
        .withConstant(p.of(Type.Bool))
        .withConstant(q.of(Type.Bool))
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
    public void complex0() {
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
    public void complex1() {
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
    
    @Test
    @Ignore ("Test not yet implemented")
    public void complex2() {
        
    }
        
    @Test
    @Ignore ("Test not yet implemented")
    public void equalsBool() {
        
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void equalsNotBool() {
        
    }
    
    @Test
    @Ignore ("Test not yet implemented")
    public void atomicArguments() {
        
    }
}
