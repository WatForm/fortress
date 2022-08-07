import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.*;
import java.util.function.*;
import java.io.*;

public class InfiniteRay {
    public static void main(String[] args) throws IOException {
        if(args.length < 1) {
            System.err.println("Please include number of vertices");
            System.exit(1);
        }
        int numVertices = Integer.parseInt(args[0]);
        
        // Create Sorts
        Sort V = Sort.mkSortConst("V"); // Vertices
        
        // Create declaration for adjacency relation
        // Adj: V x V -> Bool
        FuncDecl Adj = FuncDecl.mkFuncDecl("Adj", V, V, Sort.Bool());
        
        // Create variables to use in axioms
        Var u = mkVar("u");
        Var v = mkVar("v");
        Var x = mkVar("x");
        Var y = mkVar("y");
        Var x1 = mkVar("x1");
        Var x2 = mkVar("x2");
        Var x3 = mkVar("x3");
        
        // Create axioms
        
        // G is loopless
        Term loopless = mkForall(v.of(V), mkNot(mkApp("Adj", v, v)));
        
        // G is undirected
        Term undirected = mkForall(List.of(u.of(V), v.of(V)),
            mkImp(mkApp("Adj", u, v), mkApp("Adj", v, u)));
        
        // There is a special vertex w of degree exactly one.
        Var w = mkVar("w"); // Create constant w
        Term degreeOneW = mkExists(x.of(V),
            mkAnd(
                mkApp("Adj", x, w),
                mkForall(y.of(V), mkImp(mkApp("Adj", y, w), mkEq(y, x)))));
                
        // Every vertex that is not w has degree exactly two
        // Java function to help say "z has degree exactly two"
        java.util.function.Function<Var, Term> degreeExactlyTwo = (z) -> {
            // Assert z is not a variable introduced here for quantification
            assert ! z.equals(x1);
            assert ! z.equals(x2);
            assert ! z.equals(x3);
            return mkExists(List.of(x1.of(V), x2.of(V)),
                mkAnd(
                    mkNot(mkEq(x1, x2)),
                    mkApp("Adj", z, x1),
                    mkApp("Adj", z, x2),
                    mkForall(x3.of(V), mkImp(
                        mkApp("Adj", z, x3),
                        mkOr(mkEq(x1, x3), mkEq(x2, x3))))));
            
        };
        Term elseDegreeTwo = mkForall(u.of(V),
            mkImp(
                mkNot(mkEq(u, w)),
                // Degree exactly two
                degreeExactlyTwo.apply(u)));
                
        // Begin with the empty theory
        Theory rayTheory = Theory.empty()
        // Add sorts
            .withSorts(V)
        // Add relation declaration
            .withFunctionDeclarations(Adj)
        // Add constant declaration
            .withConstant(w.of(V))
        // Add constraints
            .withAxiom(loopless)
            .withAxiom(undirected)
            .withAxiom(degreeOneW)
            .withAxiom(elseDegreeTwo);
            
        // Initialize a model finder
        try(ModelFinder finder = ModelFinder.createDefault()){
            // Set the theory of the model finder
            finder.setTheory(rayTheory);
            
            // Set the scopes of the model finder
            finder.setExactScope(V, numVertices);
            
            // Check if all axioms in the theory are satisfiable
            ModelFinderResult result = finder.checkSat();
            
            System.out.println("numVertices: " + numVertices);
            System.out.println("Satisiable?: " + result.toString());
            
            // Print out model if it exists
            if(result.equals(ModelFinderResult.Sat())) {
                System.out.println(finder.viewModel());
            }
        }
    }
}
