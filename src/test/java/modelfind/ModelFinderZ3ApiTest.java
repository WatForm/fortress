import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.modelfind.*;
import fortress.transformers.*;

import java.util.List;
import java.io.*;
import java.util.Map;

public class ModelFinderZ3ApiTest {
    
    Var p = Term.mkVar("p");
    Var q = Term.mkVar("q");
    Var x = Term.mkVar("x");
    Var socrates = Term.mkVar("socrates");
    
    Type U = Type.mkTypeConst("U");
    
    FuncDecl Human = FuncDecl.mkFuncDecl("Human", U, Type.Bool());
    FuncDecl Mortal = FuncDecl.mkFuncDecl("Mortal", U, Type.Bool());
    
    // Propositional tests
    
    @Test
    public void propSat1() throws IOException {
        Theory theory = Theory.empty()
            .withConstant(p.of(Type.Bool()))
            .withAxiom(Term.mkAnd(p, p));
            
        
        ModelFinder finder = new ModelFinder(
            new UnscopedTransformer(),
            new Z3ApiSolver());
        
        assertEquals(ModelFinder.Result.SAT, finder.findModel(theory, 5000));
    }
    
    @Test
    public void propUnsat1() throws IOException {
        Theory theory = Theory.empty()
            .withConstant(p.of(Type.Bool()))
            .withAxiom(Term.mkAnd(p, Term.mkNot(p)));
        
        ModelFinder finder = new ModelFinder(
            new UnscopedTransformer(),
            new Z3ApiSolver());
        
        assertEquals(ModelFinder.Result.UNSAT, finder.findModel(theory, 5000));
    }
    
    @Test
    public void propUnsat2() throws IOException {
        Theory theory = Theory.empty()
            .withConstants(p.of(Type.Bool()), q.of(Type.Bool()))
            .withAxiom(Term.mkNot(Term.mkImp(Term.mkAnd(p, q), q)));
        
        ModelFinder finder = new ModelFinder(
            new UnscopedTransformer(),
            new Z3ApiSolver());
        
        assertEquals(ModelFinder.Result.UNSAT, finder.findModel(theory, 5000));
    }
    
    @Test
    public void propSat2() throws IOException {
        Theory theory = Theory.empty()
            .withConstants(p.of(Type.Bool()), q.of(Type.Bool()))
            .withAxiom(Term.mkNot(Term.mkImp(Term.mkOr(p, q), q)));
        
        ModelFinder finder = new ModelFinder(
            new UnscopedTransformer(),
            new Z3ApiSolver());
        
        assertEquals(ModelFinder.Result.SAT, finder.findModel(theory, 5000));
    }
    
    // EUF tests
    
    // FOL tests
    
    @Test
    public void socratesScope3() throws IOException {
        Term premise1 = Term.mkForall(x.of(U), Term.mkImp(Term.mkApp("Human", x), Term.mkApp("Mortal", x)));
        Term premise2 = Term.mkApp("Human", socrates);
        Term conjecture = Term.mkApp("Mortal", socrates);
        
        Theory theory = Theory.empty()
            .withType(U)
            .withConstant(socrates.of(U))
            .withFunctionDeclarations(Human, Mortal)
            .withAxiom(premise1)
            .withAxiom(premise2)
            .withAxiom(Term.mkNot(conjecture));
            
        ModelFinder finder = new ModelFinder(
            TheoryTransformer.rangeEUF(Map.of(U, 3)),
            new Z3ApiSolver());
            
        StringWriter log = new StringWriter();
        
        ModelFinder.Result result = finder.findModel(theory, 5000, log, /* debug */ true);
        
        assertEquals(log.toString(), ModelFinder.Result.UNSAT, result);
    }
}
