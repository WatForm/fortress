import org.scalatest._

import fortress.msfol._
import fortress.msfol.Term._
import fortress.msfol.Sort._
import fortress.msfol.FuncDecl._
import fortress.solverinterface._
import fortress.modelfind._
import fortress.util.Milliseconds

import scala.util.Using

class Z3ApiSolverTest extends UnitSuite {
    
    val p = mkVar("p")
    val q = mkVar("q")

    val theory = Theory.empty
        .withConstants(p of Bool, q of Bool)
        .withAxiom(p and q)
        
    val timeout = new Milliseconds(10000)
        
    test("basic solve") {
        Using.resource(new Z3ApiSolver) { solver => {
            solver.setTheory(theory)
            solver.solve(timeout) should be (ModelFinderResult.Sat)
        }}
    }
    
    test("basic solution") {
        Using.resource(new Z3ApiSolver) { solver => {
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
