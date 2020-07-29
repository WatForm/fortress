import org.scalatest._

import fortress.msfol._
import fortress.msfol.Term._
import fortress.msfol.Sort._
import fortress.msfol.FuncDecl._
import fortress.solverinterface._
import fortress.modelfind._
import fortress.util.Milliseconds

import scala.util.Using

class ProcessBuilderSolverTest extends UnitSuite {
    
    val x = mkVar("x")
    val y = mkVar("y")
    val axiom1 = mkImp(x,y)
    val axiom2 = mkImp(y,mkNot(x))

    val theory = Theory.empty
        .withConstants(x of Bool, y of Bool)
        .withAxiom(axiom1)
        .withAxiom(axiom2)
        
    val timeout = new Milliseconds(1000)
        
    test("cvc4 basic incremental solve") {
        Using.resource(new CVC4CliSolver) { solver => {
            solver.open()
            solver.setTheory(theory)
            solver.solve(timeout) should be (ModelFinderResult.Sat)
            solver.addAxiom(x)
            solver.solve(timeout) should be (ModelFinderResult.Unsat)
        }}
    }
    
    test("z3 basic incremental solve") {
        Using.resource(new Z3CliSolver) { solver => {
            solver.open()
            solver.setTheory(theory)
            solver.solve(timeout) should be (ModelFinderResult.Sat)
            solver.addAxiom(x)
            solver.solve(timeout) should be (ModelFinderResult.Unsat)
        }}
    }
    
    val predicate = mkFuncDecl("p", IntSort, Bool)
    val theory2 = Theory.empty
        .withConstants(x of IntSort, y of IntSort)
        .withFunctionDeclaration(predicate)
        .withAxiom(
            mkApp("p", x)
        )
        .withAxiom(
            mkNot(mkApp("p", y))
        )
        
    test("cvc4 solve 2 different theories with 1 solver") {
        pending
        Using.resource(new CVC4CliSolver) { solver => {
            // solver.solve(theory, timeout, Seq()) should be (ModelFinderResult.Sat);
            // solver.solve(theory2, timeout, Seq()) should be (ModelFinderResult.Sat);
        }}
    }
    
    test("z3 solve 2 different theories with 1 solver") {
        pending
        Using.resource(new Z3CliSolver) { solver => {
            // solver.solve(theory, timeout, Seq()) should be (ModelFinderResult.Sat);
            // solver.solve(theory2, timeout, Seq()) should be (ModelFinderResult.Sat);
        }}
    }
}
