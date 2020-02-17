import fortress.msfol.*;
import fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

/* Implementation of 4 x 4 Sudoku in Fortress */
public class Sudoku {

    public static void main(String[] args) {
        
        // Initialize sort (Number)
        Sort number = Sort.mkSortConst("Number");
 
        // Initialize variables (n1, n2, n3, n4)
        Var n1 = Term.mkVar("n1");
        Var n2 = Term.mkVar("n2");
        Var n3 = Term.mkVar("n3");
        Var n4 = Term.mkVar("n4");
   
        /* Initialize function (data : Number x Number -> Number) where the 
        arguments represent the row and column number and the return value
        is the value stored in that cell */
        FuncDecl data = FuncDecl.mkFuncDecl("data", number, number, number);

        // Initialize a list of 4 enum values (or set scope of Number as 4)
        List<EnumValue> numbers = List.of(
            Term.mkEnumValue("N1"), 
            Term.mkEnumValue("N2"), 
            Term.mkEnumValue("N3"), 
            Term.mkEnumValue("N4"));

        // Initialize a theory with given sort, constants and function
        // Note : Constants are variables with assigned type (called AnnotatedVar) 
        Theory theory = Theory.empty()
            .withEnumSort(number, numbers)
            .withConstants(n1.of(number), n2.of(number), n3.of(number), n4.of(number))
            .withFunctionDeclarations(data);

        // Add axiom that each constant corresponds to a specific enum value
        theory = theory.withAxiom(Term.mkEq(n1, numbers.get(0)));
        theory = theory.withAxiom(Term.mkEq(n2, numbers.get(1)));
        theory = theory.withAxiom(Term.mkEq(n3, numbers.get(2)));
        theory = theory.withAxiom(Term.mkEq(n4, numbers.get(3)));

        // Add axiom that all numbers in a given row are distinct
        Var row = Term.mkVar("row");
        theory = theory.withAxiom(Term.mkForall(row.of(number), Term.mkDistinct(
            Term.mkApp("data", row, n1),
            Term.mkApp("data", row, n2),
            Term.mkApp("data", row, n3),
            Term.mkApp("data", row, n4))));

        // Add axiom that all numbers in a given column are distinct
        Var col = Term.mkVar("col");
        theory = theory.withAxiom(Term.mkForall(col.of(number), Term.mkDistinct(
            Term.mkApp("data", n1, col),
            Term.mkApp("data", n2, col),
            Term.mkApp("data", n3, col),
            Term.mkApp("data", n4, col))));

        // Add axiom that all numbers in the top left 2x2 region are distinct
        theory = theory.withAxiom(Term.mkDistinct(
            Term.mkApp("data", n1, n1),
            Term.mkApp("data", n1, n2),
            Term.mkApp("data", n2, n1),
            Term.mkApp("data", n2, n2)));
        // Add axiom that all numbers in the bottom left 2x2 region are distinct
        theory = theory.withAxiom(Term.mkDistinct(
            Term.mkApp("data", n3, n1),
            Term.mkApp("data", n3, n2),
            Term.mkApp("data", n4, n1),
            Term.mkApp("data", n4, n2)));
        // Add axiom that all numbers in the top right 2x2 region are distinct
        theory = theory.withAxiom(Term.mkDistinct(
            Term.mkApp("data", n1, n3),
            Term.mkApp("data", n1, n4),
            Term.mkApp("data", n2, n3),
            Term.mkApp("data", n2, n4)));
        // Add axiom that all numbers in the bottom right 2x2 region are distinct
        theory = theory.withAxiom(Term.mkDistinct(
            Term.mkApp("data", n3, n3),
            Term.mkApp("data", n3, n4),
            Term.mkApp("data", n4, n3),
            Term.mkApp("data", n4, n4)));

        Theory emptyTheory = theory;

        // Add clues as axioms
        theory = theory.withAxiom(Term.mkEq(n3, Term.mkApp("data", n1, n1)));
        theory = theory.withAxiom(Term.mkEq(n4, Term.mkApp("data", n1, n2)));
        theory = theory.withAxiom(Term.mkEq(n2, Term.mkApp("data", n2, n2)));
        theory = theory.withAxiom(Term.mkEq(n1, Term.mkApp("data", n1, n3)));
        theory = theory.withAxiom(Term.mkEq(n1, Term.mkApp("data", n4, n2)));
        theory = theory.withAxiom(Term.mkEq(n2, Term.mkApp("data", n3, n3)));
        theory = theory.withAxiom(Term.mkEq(n4, Term.mkApp("data", n4, n3)));
        theory = theory.withAxiom(Term.mkEq(n3, Term.mkApp("data", n4, n4)));

        // Initialize a model finder 
        ModelFinder finder = ModelFinder.createDefault();
        try {
            StringWriter log = new StringWriter();
            finder.setOutput(log);
            // Assign theory to the model finder 
            finder.setTheory(theory);
            // Check if all axioms in the theory are satisfiable 
            ModelFinderResult res = finder.checkSat();
            System.out.println(log.toString());
            // Get satisfiable instance back from the model finder 
            System.out.println(finder.viewModel());

            // Count the total number of possible sudokus
            System.out.println("Counting all valid sudokus...");
            System.out.println("Total models found: " + finder.countValidModels(emptyTheory));
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
