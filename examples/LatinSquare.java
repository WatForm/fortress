import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

public class LatinSquare {
    public static void main(String[] args) {
        if(args.length < 1) {
            System.err.println("Please include grid length");
            System.exit(1);
        }
        int gridLength = Integer.parseInt(args[0]);
        
        // Create Sorts
        Sort Row = Sort.mkSortConst("Row"); // Rows
        Sort Col = Sort.mkSortConst("Col"); // Columns
        Sort Num = Sort.mkSortConst("Num"); // Number entries
        
        // Create declaration for entry function
        // entry: Row x Col -> Num
        FuncDecl entry = FuncDecl.mkFuncDecl("entry", Row, Col, Num);
        
        // Create variables to use in axioms
        Var r = mkVar("r");
        Var r1 = mkVar("r1");
        Var r2 = mkVar("r2");
        Var c = mkVar("c");
        Var c1 = mkVar("c1");
        Var c2 = mkVar("c2");
        
        // Create axioms
        // For each row, every column gives a different number
        Term rowConstraint = mkForall(List.of(r.of(Row), c1.of(Col), c2.of(Col)),
            mkImp(
                mkEq(mkApp("entry", r, c1), mkApp("entry", r, c2)),
                mkEq(c1, c2)
                ));
        // For each column, every row gives a different number
        Term colConstraint = mkForall(List.of(c.of(Col), r1.of(Row), r2.of(Row)),
            mkImp(
                mkEq(mkApp("entry", r1, c), mkApp("entry", r2, c)),
                mkEq(r1, r2)
                ));
                
        // Begin with the empty theory
        Theory latinSquareTheory =  Theory.empty()
        // Add sorts
            .withSorts(Row, Col, Num)
        // Add declarations
            .withFunctionDeclarations(entry)
        // Add constraints
            .withAxiom(rowConstraint)
            .withAxiom(colConstraint);
            
        // Initialize a model finder 
        ModelFinder finder = ModelFinder.createDefault();
        
        // Set the theory of the model finder
        finder.setTheory(latinSquareTheory);
        
        // Set the scopes of the model finder
        finder.setAnalysisScope(Row, gridLength);
        finder.setAnalysisScope(Col, gridLength);
        finder.setAnalysisScope(Num, gridLength);
        
        // Check if all axioms in the theory are satisfiable 
        ModelFinderResult result = finder.checkSat();
        
        System.out.println("Grid Size: " + gridLength);
        System.out.println("satisiable?: " + result.toString());
        
        // Print out model if it exists
        if(result.equals(ModelFinderResult.Sat())) {
            System.out.println(finder.viewModel());

            // Count the total number of models
            System.out.println("Counting all valid solutions...");
            System.out.println("Total models found: " + finder.countValidModels(latinSquareTheory));
        }
    }
}
