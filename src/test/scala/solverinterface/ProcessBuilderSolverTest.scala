import org.scalatest._

import fortress.msfol._
import fortress.msfol.Term._
import fortress.msfol.Sort._
import fortress.solverinterface._
import fortress.modelfind._
import fortress.util.Milliseconds

class ProcessBuilderSolverTest extends UnitSuite {
    test("cvc 4 basic incremental solve") {
        val a = mkVar("a")
        val b = mkVar("b")
        val axiom1 = mkImp(a,b)
        val axiom2 = mkImp(b,mkNot(a))

        val theory = Theory.empty
            .withConstants(a of Bool, b of Bool)
            .withAxiom(axiom1)
            .withAxiom(axiom2);
            
        val solver = new CVC4CliSolver;

        val timeout = new Milliseconds(1000);

        solver.solve(theory, timeout, Seq()) should be (ModelFinderResult.Sat);
        solver.addAxiom(a, timeout) should be (ModelFinderResult.Unsat);
    }
}
