import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.solverinterface.CVC4CliSolver;
import fortress.operations.*;
import fortress.util.Milliseconds;

import java.io.IOException;

class BasicCVC4{
    public static void main(String[] args) throws IOException {
        Var a = mkVar("a");
        Var b = mkVar("b");
        Term axiom1 = mkImp(a,b);
        Term axiom2 = mkImp(b,mkNot(a));
        
        Theory theory = Theory.empty()
            .withConstants(a.of(Sort.Bool()), b.of(Sort.Bool()))
            .withAxiom(axiom1)
            .withAxiom(axiom2);
            
        CVC4CliSolver solver = new CVC4CliSolver();
        
        Milliseconds timeout = new Milliseconds(1000);
        
        System.out.println("Solving: " + new TheoryOps(theory).smtlib());
        System.out.println("result: " + solver.solve(theory, timeout, null));
        System.out.println("Adding: " + new TermOps(a).smtlibAssertion());
        System.out.println("new result: " + solver.addAxiom(a, timeout));
    }
}
