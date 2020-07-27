import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

public class NonAbelianGroup {
    public static void main(String[] args) throws IOException {
        if(args.length < 1) {
            System.err.println("Please include group size");
            System.exit(1);
        }
        int groupSize = Integer.parseInt(args[0]);
        
        // Create Sorts
        Sort G = Sort.mkSortConst("G"); // Group
        
        // Create declaration for group operation f
        // f: G x G -> G
        FuncDecl entry = FuncDecl.mkFuncDecl("f", G, G, G);
        
        // Create variables to use in axioms
        Var x = mkVar("x");
        Var y = mkVar("y");
        Var z = mkVar("z");
        
        // Create identity constant
        Var e = mkVar("e");
        
        // Create group axioms
        // Associativity
        Term associativity = mkForall(List.of(x.of(G), y.of(G), z.of(G)),
            mkEq(
                mkApp("f", mkApp("f", x, y), z),
                mkApp("f", x, mkApp("f", y, z))));
        // Identity
        Term identity = mkForall(x.of(G),
            mkAnd(
                mkEq(mkApp("f", x, e), x),
                mkEq(mkApp("f", e, x), x)));
        // Inverse
        Term inverse = mkForall(x.of(G), mkExists(y.of(G),
            mkAnd(
                mkEq(mkApp("f", x, y), e),
                mkEq(mkApp("f", y, x), e))));
                
        // Begin with the empty theory
        Theory groupTheory = Theory.empty()
        // Add sorts
            .withSort(G)
        // Add function declarations
            .withFunctionDeclarations(entry)
        // Add constant declaration
            .withConstant(e.of(G))
        // Add constraints
            .withAxiom(associativity)
            .withAxiom(identity)
            .withAxiom(inverse);
        
        // Abelian axiom
        Term abelian = mkForall(List.of(x.of(G), y.of(G)),
            mkEq(
                mkApp("f", x, y),
                mkApp("f", y, x)));
        
        // Create theory of non-abelian groups
        Theory nonAbelianGroupTheory = groupTheory
            .withAxiom(mkNot(abelian));
            
        // Initialize a model finder
        try(ModelFinder finder = ModelFinder.createDefault()) {
            // Set the theory of the model finder
            finder.setTheory(nonAbelianGroupTheory);
            
            // Set the scopes of the model finder
            finder.setAnalysisScope(G, groupSize);
            
            // Check if all axioms in the theory are satisfiable
            ModelFinderResult result = finder.checkSat();
            
            System.out.println("Group Size: " + groupSize);
            System.out.println("Satisiable?: " + result.toString());
            
            // Print out model if it exists
            if(result.equals(ModelFinderResult.Sat())) {
                System.out.println(finder.viewModel());
            }
        }
    }
}
