import org.scalatest._

import fortress.msfol._
import fortress.modelfind._
import fortress.transformers._

class ModelFinderZ3ApiTest extends UnitSuite {
    
    val p = Var("p")
    val q = Var("q")
    val x = Var("x")
    val socrates = Var("socrates")
    
    val U = Sort.mkSortConst("U")
    
    val Human = FuncDecl.mkFuncDecl("Human", U, Sort.Bool)
    val Mortal = FuncDecl.mkFuncDecl("Mortal", U, Sort.Bool)
    
    // Propositional tests
    
    test("prop sat 1") {
        val theory = Theory.empty
            .withConstant(p.of(Sort.Bool))
            .withAxiom(And(p, p))
        
        val finder = ModelFinder.createDefault
        finder.setTheory(theory)
        
        finder.checkSat should be (ModelFinderResult.Sat)
    }
    
    test("prop unsat 1") {
        val theory = Theory.empty
            .withConstant(p.of(Sort.Bool))
            .withAxiom(And(p, Not(p)))
        
        val finder = ModelFinder.createDefault
        finder.setTheory(theory)
        
        finder.checkSat should be (ModelFinderResult.Unsat)
    }
    
    test("prop unsat 2") {
        val theory = Theory.empty
            .withConstants(p.of(Sort.Bool), q.of(Sort.Bool))
            .withAxiom(Not(Implication(And(p, q), q)))
        
        val finder = ModelFinder.createDefault
        finder.setTheory(theory)
        
        finder.checkSat should be (ModelFinderResult.Unsat)
    }
    
    test("prop sat 2") {
        val theory = Theory.empty
            .withConstants(p.of(Sort.Bool), q.of(Sort.Bool))
            .withAxiom(Not(Implication(Or(p, q), q)))
        
        val finder = ModelFinder.createDefault
        finder.setTheory(theory)
        
        finder.checkSat should be (ModelFinderResult.Sat)
    }
    
    // EUF tests
    
    // FOL tests
    
    test("socrates scope 3") {
        val premise1 = Forall(x.of(U), Implication(App("Human", x), App("Mortal", x)))
        val premise2 = App("Human", socrates)
        val conjecture = App("Mortal", socrates)
        
        val theory = Theory.empty
            .withSort(U)
            .withConstant(socrates.of(U))
            .withFunctionDeclarations(Human, Mortal)
            .withAxiom(premise1)
            .withAxiom(premise2)
            .withAxiom(Not(conjecture))
            
        val finder = ModelFinder.createDefault
        finder.setTheory(theory)
        finder.setAnalysisScope(U, 3)
        finder.checkSat should be (ModelFinderResult.Unsat)
    }
}
