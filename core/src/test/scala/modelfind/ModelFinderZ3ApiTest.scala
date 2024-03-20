import org.scalatest._

import fortress.msfol._
import fortress.modelfind._
import fortress.transformers._

import scala.util.Using

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
            .withConstantDeclaration(p.of(Sort.Bool))
            .withAxiom(And(p, p))
        
        Using.resource(ModelFinder.createDefault) { finder => {
            finder.setTheory(theory)
            
            finder.checkSat(false) should be (ModelFinderResult.Sat)
        }}
    }
    
    test("prop unsat 1") {
        val theory = Theory.empty
            .withConstantDeclaration(p.of(Sort.Bool))
            .withAxiom(And(p, Not(p)))
        
        Using.resource(ModelFinder.createDefault) { finder => {
            finder.setTheory(theory)
            
            finder.checkSat(false) should be (ModelFinderResult.Unsat)
        }}
    }
    
    test("prop unsat 2") {
        val theory = Theory.empty
            .withConstantDeclarations(p.of(Sort.Bool), q.of(Sort.Bool))
            .withAxiom(Not(Implication(And(p, q), q)))
        
        Using.resource(ModelFinder.createDefault) { finder => {
            finder.setTheory(theory)
            
            finder.checkSat(false) should be (ModelFinderResult.Unsat)
        }}
    }
    
    test("prop sat 2") {
        val theory = Theory.empty
            .withConstantDeclarations(p.of(Sort.Bool), q.of(Sort.Bool))
            .withAxiom(Not(Implication(Or(p, q), q)))
        
        Using.resource(ModelFinder.createDefault) { finder => {
            finder.setTheory(theory)
            
            finder.checkSat(false) should be (ModelFinderResult.Sat)
        }}
    }
    
    // EUF tests
    
    // FOL tests
    
    test("socrates scope 3") {
        val premise1 = Forall(x.of(U), Implication(App("Human", x), App("Mortal", x)))
        val premise2 = App("Human", socrates)
        val conjecture = App("Mortal", socrates)
        
        val theory = Theory.empty
            .withSort(U)
            .withConstantDeclaration(socrates.of(U))
            .withFunctionDeclarations(Human, Mortal)
            .withAxiom(premise1)
            .withAxiom(premise2)
            .withAxiom(Not(conjecture))
            
        Using.resource(ModelFinder.createDefault) { finder => {
            finder.setTheory(theory)
            finder.setExactScope(U, 3)
            finder.checkSat(false) should be (ModelFinderResult.Unsat)
        }}
    }
}
