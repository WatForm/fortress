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
        
        ModelFinder finder = ModelFinder.createDefault();
        
        assertEquals(ModelFinder.Result.SAT, finder.checkSat(theory));
    }
    
    @Test
    public void propUnsat1() throws IOException {
        Theory theory = Theory.empty()
            .withConstant(p.of(Type.Bool()))
            .withAxiom(Term.mkAnd(p, Term.mkNot(p)));
        
        ModelFinder finder = ModelFinder.createDefault();
        
        assertEquals(ModelFinder.Result.UNSAT, finder.checkSat(theory));
    }
    
    @Test
    public void propUnsat2() throws IOException {
        Theory theory = Theory.empty()
            .withConstants(p.of(Type.Bool()), q.of(Type.Bool()))
            .withAxiom(Term.mkNot(Term.mkImp(Term.mkAnd(p, q), q)));
        
        ModelFinder finder = ModelFinder.createDefault();
        
        assertEquals(ModelFinder.Result.UNSAT, finder.checkSat(theory));
    }
    
    @Test
    public void propSat2() throws IOException {
        Theory theory = Theory.empty()
            .withConstants(p.of(Type.Bool()), q.of(Type.Bool()))
            .withAxiom(Term.mkNot(Term.mkImp(Term.mkOr(p, q), q)));
        
        ModelFinder finder = ModelFinder.createDefault();
        
        assertEquals(ModelFinder.Result.SAT, finder.checkSat(theory));
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
            
        ModelFinder finder = ModelFinder.createDefault();
        finder.setAnalysisScope(U, 3);
        ModelFinder.Result result = finder.checkSat(theory);
        assertEquals(ModelFinder.Result.UNSAT, result);
    }
}
