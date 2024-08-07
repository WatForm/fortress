import org.scalatest._

import fortress.msfol._
import fortress.msfol.Term._
import fortress.msfol.Sort._
import fortress.msfol.FuncDecl._
import fortress.solvers._
import fortress.modelfinders._
import fortress.util.Milliseconds

import scala.util.Using

class ProcessBuilderSolverTest extends UnitSuite {
    
    val x = mkVar("x")
    val y = mkVar("y")
    val axiom1 = mkImp(x,y)
    val axiom2 = mkImp(y,mkNot(x))

    val theory = Theory.empty
        .withConstantDeclarations(x of Bool, y of Bool)
        .withAxiom(axiom1)
        .withAxiom(axiom2)
        
    val timeout = new Milliseconds(1000)
        
    test("cvc5 basic incremental solve") {
        Using.resource(new CVC5CliSolver) { solver => {
            solver.setTheory(theory)
            solver.solve(timeout) should be (ModelFinderResult.Sat)
            solver.addAxiom(x)
            solver.solve(timeout) should be (ModelFinderResult.Unsat)
        }}
    }
    
    test("z3 basic incremental solve") {
        Using.resource(new Z3NonIncCliSolver) { solver => {
            solver.setTheory(theory)
            solver.solve(timeout) should be (ModelFinderResult.Sat)
            solver.addAxiom(x)
            solver.solve(timeout) should be (ModelFinderResult.Unsat)
        }}
    }
    
    val predicate = mkFuncDecl("p", IntSort, Bool)
    val theory2 = Theory.empty
        .withConstantDeclarations(x of IntSort, y of IntSort)
        .withFunctionDeclaration(predicate)
        .withAxiom(
            mkApp("p", x)
        )
        .withAxiom(
            mkNot(mkApp("p", y))
        )
    
    // Don't know if we should support this behaviour
    test("cvc5 solve 2 different theories with 1 solver") {
        pending
        Using.resource(new CVC5CliSolver) { solver => {
            // solver.solve(theory, timeout, Seq()) should be (ModelFinderResult.Sat);
            // solver.solve(theory2, timeout, Seq()) should be (ModelFinderResult.Sat);
        }}
    }
    
    test("z3 solve 2 different theories with 1 solver") {
        pending
        Using.resource(new Z3NonIncCliSolver) { solver => {
            // solver.solve(theory, timeout, Seq()) should be (ModelFinderResult.Sat);
            // solver.solve(theory2, timeout, Seq()) should be (ModelFinderResult.Sat);
        }}
    }
}

class Z3ProcessBuilderTest2 extends UnitSuite {
    
    val p = mkVar("p")
    val q = mkVar("q")

    val theory = Theory.empty
        .withConstantDeclarations(p of Bool, q of Bool)
        .withAxiom(p and q)
        
    val timeout = new Milliseconds(10000)
        
    test("basic solve") {
        Using.resource(new Z3NonIncCliSolver) { solver => {
            solver.setTheory(theory)
            solver.solve(timeout) should be (ModelFinderResult.Sat)
        }}
    }
    
    test("basic solution") {
        Using.resource(new Z3NonIncCliSolver) { solver => {
            solver.setTheory(theory)
            solver.solve(timeout) should be (ModelFinderResult.Sat)
            val soln = solver.solution
            soln.constantInterpretations should be { Map(
                (p of Bool) -> Top,
                (q of Bool) -> Top
            )}
        }}
    }
}