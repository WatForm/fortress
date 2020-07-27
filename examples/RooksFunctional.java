import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

public class RooksFunctional {
    public static void main(String[] args) throws IOException {
        if(args.length < 1) {
            System.err.println("Please include grid size");
            System.exit(1);
        }
        int gridSize = Integer.parseInt(args[0]);
        
        // Create Sorts
        Sort Row = Sort.mkSortConst("Row"); // Rows
        Sort Col = Sort.mkSortConst("Col"); // Columns
        
        // Create declaration for rook assignment function
        // Rook: Row -> Col
        // Rook(i) = j means that there is a rook in row i, column j
        // Since Q is a function, it means that every row has a rook
        // and that no row has more than one rook
        FuncDecl Rook = FuncDecl.mkFuncDecl("Rook", Row, Col);
        
        // Create variables to use in axioms
        Var r = mkVar("r");
        Var c = mkVar("c");
        Var r1 = mkVar("r1");
        Var r2 = mkVar("r2");
        
        // Create axioms
        // "Each column has a rook in it"
        Term colConstraint1 = mkForall(c.of(Col), mkExists(r.of(Row), mkEq(mkApp("Rook", r), c)));
        // "At most one rook in each column"
        Term colConstraint2 = mkForall(List.of(r1.of(Row), r2.of(Row)),
            mkImp(
                mkEq(mkApp("Rook", r1), mkApp("Rook", r2)),
                mkEq(r1, r2)));
                
        // Begin with the empty theory
        Theory rookTheory =  Theory.empty()
        // Add sorts
            .withSorts(Row, Col)
        // Add declarations
            .withFunctionDeclarations(Rook)
        // Add constraints
            .withAxiom(colConstraint1)
            .withAxiom(colConstraint2);
            
        // Initialize a model finder
        try(ModelFinder finder = ModelFinder.createDefault()) {
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
            }
        }
    }
}
