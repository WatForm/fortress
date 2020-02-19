import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

public class RooksRelational {
    public static void main(String[] args) {
        if(args.length < 1) {
            System.err.println("Please include grid size");
            System.exit(1);
        }
        int gridSize = Integer.parseInt(args[0]);
        
        // Create Sorts
        Sort Row = Sort.mkSortConst("Row"); // Rows
        Sort Col = Sort.mkSortConst("Col"); // Columns
        
        // Create declaration for rook assignment predicate
        // Rook: Row x Col -> Bool
        FuncDecl Rook = FuncDecl.mkFuncDecl("Rook", Row, Col, Sort.Bool());
        
        // Create variables to use in axioms
        Var r = mkVar("r");
        Var r1 = mkVar("r1");
        Var r2 = mkVar("r2");
        Var c = mkVar("c");
        Var c1 = mkVar("c1");
        Var c2 = mkVar("c2");
        
        // Create axioms
        // "Each row has a rook in it"
        Term rowConstraint1 = mkForall(r.of(Row), mkExists(c.of(Col), mkApp("Rook", r, c)));
        // "At most one rook in each row"
        Term rowConstraint2 = mkForall(List.of(r.of(Row), c1.of(Col), c2.of(Col)),
            mkImp(
                mkAnd(mkApp("Rook", r, c1), mkApp("Rook", r, c2)),
                mkEq(c1, c2)));
        // "Each column has a rook in it"
        Term colConstraint1 = mkForall(c.of(Col), mkExists(r.of(Row), mkApp("Rook", r, c)));
        // "At most one rook in each column"
        Term colConstraint2 = mkForall(List.of(c.of(Col), r1.of(Row), r2.of(Row)),
            mkImp(
                mkAnd(mkApp("Rook", r1, c), mkApp("Rook", r2, c)),
                mkEq(r1, r2)));
                
        // Begin with the empty theory
        Theory rookTheory =  Theory.empty()
        // Add sorts
            .withSorts(Row, Col)
        // Add declarations
            .withFunctionDeclarations(Rook)
        // Add constraints
            .withAxiom(rowConstraint1)
            .withAxiom(rowConstraint2)
            .withAxiom(colConstraint1)
            .withAxiom(colConstraint2);
            
        // Initialize a model finder 
        ModelFinder finder = ModelFinder.createDefault();
        
        // Set the theory of the model finder
        finder.setTheory(rookTheory);
        
        // Set the scopes of the model finder
        finder.setAnalysisScope(Row, gridSize);
        finder.setAnalysisScope(Col, gridSize);
        
        // Check if all axioms in the theory are satisfiable 
        ModelFinderResult result = finder.checkSat();
        
        System.out.println("Grid Size: " + gridSize);
        System.out.println("Satisiable?: " + result.toString());
        
        // Print out model if it exists
        if(result.equals(ModelFinderResult.Sat())) {
            System.out.println(finder.viewModel());

            // Count the total number of models
            System.out.println("Counting all valid solutions...");
            System.out.println("Total models found: " + finder.countValidModels(rookTheory));
        }
    }
}
