import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

/*
    This example describes the classic Barber problem:
        The barbers in town only do hair cut for people who do not cut their own hair.
        So who cut hair for the barber?
    This problem is satisfiable when there is no barber or more than one barber in town, unsatisfiable otherwise.
*/

public class Barber {
    public static void main(String[] args) throws IOException {
        if(args.length < 1) {
            System.err.println("Please include barberNum");
            System.exit(1);
        }
        int barberNum = Integer.parseInt(args[0]);

        // Create Sorts
        Sort B = Sort.mkSortConst("B"); // Barbers

        // Create declaration for barber assignment assignment function
        // f: B -> B
        FuncDecl cut = FuncDecl.mkFuncDecl("cut", B, B);
        FuncDecl inTown = FuncDecl.mkFuncDecl("inTown", B, Sort.Bool());

        // Create variables to use in axioms
        Var b = mkVar("b");
        Var c = mkVar("c");

        // Create axiom

        // exist at least one barber in town
        Term axiom0 = mkExists(b.of(B), mkApp("inTown", b));

        // if a barber in town, he cannot cut himself
        Term axiom1 = mkForall(List.of(b.of(B)),
            mkImp(mkApp("inTown", b),mkNot(mkEq(mkApp("cut",b), b)))
        );

        // a barber in town can only be cut by a barber in town
        Term axiom2 = mkForall(List.of(b.of(B), c.of(B)),
            mkImp(mkApp("inTown", b),mkImp(mkEq(mkApp("cut",b), c), mkApp("inTown", c)))
        );


        // Begin with the empty theory
        Theory barberTheory =  Theory.empty()
        // Add sorts
            .withSorts(B)
        // Add declarations
            .withFunctionDeclarations(cut, inTown)
        // Add constraints
            .withAxiom(axiom0)
            .withAxiom(axiom1)
            .withAxiom(axiom2);

        try(ModelFinder finder = ModelFinder.createDefault()) {
            // Set the theory of the model finder
            finder.setTheory(barberTheory);
            
            // Set the scopes of the model finder
            finder.setAnalysisScope(B, barberNum, false);
            
            // Check if all axioms in the theory are satisfiable
            ModelFinderResult result = finder.checkSat();

            System.out.println("Satisiable?: " + result.toString());
            
            // Print out model if it exists
            if(result.equals(ModelFinderResult.Sat())) {
                System.out.println(finder.viewModel());
            }
        }
        
    }
}
