import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.Ignore;

import fortress.msfol.*;
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
    
    Sort U = Sort.mkSortConst("U");
    
    FuncDecl Human = FuncDecl.mkFuncDecl("Human", U, Sort.Bool());
    FuncDecl Mortal = FuncDecl.mkFuncDecl("Mortal", U, Sort.Bool());
    
    // Propositional tests
    
    @Test
    public void propSat1() throws IOException {
        Theory theory = Theory.empty()
            .withConstant(p.of(Sort.Bool()))
            .withAxiom(Term.mkAnd(p, p));
        
        ModelFinder finder = ModelFinder.createDefault();
        finder.setTheory(theory);
        
        assertEquals(ModelFinderResult.Sat(), finder.checkSat());
    }
    
    @Test
    public void propUnsat1() throws IOException {
        Theory theory = Theory.empty()
            .withConstant(p.of(Sort.Bool()))
            .withAxiom(Term.mkAnd(p, Term.mkNot(p)));
        
        ModelFinder finder = ModelFinder.createDefault();
        finder.setTheory(theory);
        
        assertEquals(ModelFinderResult.Unsat(), finder.checkSat());
    }
    
    @Test
    public void propUnsat2() throws IOException {
        Theory theory = Theory.empty()
            .withConstants(p.of(Sort.Bool()), q.of(Sort.Bool()))
            .withAxiom(Term.mkNot(Term.mkImp(Term.mkAnd(p, q), q)));
        
        ModelFinder finder = ModelFinder.createDefault();
        finder.setTheory(theory);
        
        assertEquals(ModelFinderResult.Unsat(), finder.checkSat());
    }
    
    @Test
    public void propSat2() throws IOException {
        Theory theory = Theory.empty()
            .withConstants(p.of(Sort.Bool()), q.of(Sort.Bool()))
            .withAxiom(Term.mkNot(Term.mkImp(Term.mkOr(p, q), q)));
        
        ModelFinder finder = ModelFinder.createDefault();
        finder.setTheory(theory);
        
        assertEquals(ModelFinderResult.Sat(), finder.checkSat());
    }
    
    // EUF tests
    
    // FOL tests
    
    @Test
    public void socratesScope3() throws IOException {
        Term premise1 = Term.mkForall(x.of(U), Term.mkImp(Term.mkApp("Human", x), Term.mkApp("Mortal", x)));
        Term premise2 = Term.mkApp("Human", socrates);
        Term conjecture = Term.mkApp("Mortal", socrates);
        
        Theory theory = Theory.empty()
            .withSort(U)
            .withConstant(socrates.of(U))
            .withFunctionDeclarations(Human, Mortal)
            .withAxiom(premise1)
            .withAxiom(premise2)
            .withAxiom(Term.mkNot(conjecture));
            
        ModelFinder finder = ModelFinder.createDefault();
        finder.setTheory(theory);
        finder.setAnalysisScope(U, 3);
        assertEquals(ModelFinderResult.Unsat(), finder.checkSat());
    }
}
