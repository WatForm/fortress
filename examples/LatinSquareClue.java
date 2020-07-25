import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

public class LatinSquareClue {
    public static void main(String[] args) throws Exception {
        int gridLength = 4;
        
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
        
        // Create clues
        // R1 x C4 |-> 1
        Term clue1 = mkEq(
            mkApp("entry", mkDomainElement(1, Row), mkDomainElement(4, Col)),
            mkDomainElement(1, Num));
        // R2 x C1 |-> 3
        Term clue2 = mkEq(
            mkApp("entry", mkDomainElement(2, Row), mkDomainElement(1, Col)),
            mkDomainElement(3, Num));
        // R3 x C3 |-> 2
        Term clue3 = mkEq(
            mkApp("entry", mkDomainElement(3, Row), mkDomainElement(3, Col)),
            mkDomainElement(2, Num));
        // R4 x C1 |-> 4
        Term clue4 = mkEq(
            mkApp("entry", mkDomainElement(4, Row), mkDomainElement(2, Col)),
            mkDomainElement(4, Num));
                
        // Begin with the empty theory
        Theory latinSquareTheory =  Theory.empty()
        // Add sorts
            .withSorts(Row, Col, Num)
        // Add declarations
            .withFunctionDeclarations(entry)
        // Add constraints
            .withAxiom(rowConstraint)
            .withAxiom(colConstraint)
        // Add clues as additional constraints
            .withAxiom(clue1)
            .withAxiom(clue2)
            .withAxiom(clue3)
            .withAxiom(clue4);
            
        // Initialize a model finder
        try(ModelFinder finder = ModelFinder.createDefault()){
            // Set the theory of the model finder
            finder.setTheory(latinSquareTheory);
            
            // Set the scopes of the model finder
            finder.setAnalysisScope(Row, gridLength);
            finder.setAnalysisScope(Col, gridLength);
            finder.setAnalysisScope(Num, gridLength);
            
            // Check if all axioms in the theory are satisfiable
            ModelFinderResult result = finder.checkSat();
            
            System.out.println("Grid Size: " + gridLength);
            System.out.println("Satisiable?: " + result.toString());
            
            // Print out model if it exists
            if(result.equals(ModelFinderResult.Sat())) {
                System.out.println(finder.viewModel());
            }
        }
    }
}
