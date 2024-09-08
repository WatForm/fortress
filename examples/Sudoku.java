import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.*;

public class Sudoku{
    public static void printSudoku(int[][] sudoku){
        for(int r = 1; r <= 9; ++r){
            for(int c = 1; c <= 9; ++c){
                String entry = sudoku[r][c] == 0 ? "-" : Integer.toString(sudoku[r][c]);
                System.out.print(entry);
                if(c%3 == 0) System.out.print(" ");
            }
            System.out.println();
            if(r%3 == 0) System.out.println();
        }
    }

    public static void main(String[] args){
        // Create a single sort
        Sort Digit = Sort.mkSortConst("Digit");

        // Create an array of all 9 digit terms and a map that maps them back to an integer for convenience
        Term[] digits = new Term[10];
        Map<Term, Integer> digitIntegers= new HashMap<>();
        for(int i=1; i<10; ++i){
            digits[i] = mkDomainElement(i, Digit);
            digitIntegers.put(digits[i], i);
        }

        // Create declaration for entry function
        // entry: Digit x Digit -> Digit
        final String entry = "entry";
        FuncDecl entryFn = FuncDecl.mkFuncDecl(entry, Digit, Digit, Digit);

        // There are 27 axioms, plus an extra axiom for each pre defined entry in the grid
        List<Term> axioms = new ArrayList<>(27);

        // The digits in each row must be distinct
        for(int r = 1; r <= 9; ++r){
            List<Term> rowTerms = new ArrayList<>(9);
            for(int c = 1; c <= 9; ++c){
                rowTerms.add(mkApp(entry, digits[r], digits[c]));
            }
            axioms.add(mkDistinct(rowTerms));
        }

        // The digits in each column must be distinct
        for(int c = 1; c <= 9; ++c){
            List<Term> colTerms = new ArrayList<>(9);
            for(int r = 1; r <= 9; ++r){
                colTerms.add(mkApp(entry, digits[r], digits[c]));
            }
            axioms.add(mkDistinct(colTerms));
        }

        // The digits in each 3x3 block must be distinct
        for(int i = 0; i < 3; ++i){
            for(int j = 0; j < 3; ++j){
                List<Term> gridTerms = new ArrayList<>(9);
                for(int k = 0; k < 3; ++k){
                    for(int l = 0; l < 3; ++l){
                        gridTerms.add(mkApp(entry, digits[i*3 + k + 1], digits[j*3 + l + 1]));
                    }
                }
                axioms.add(mkDistinct(gridTerms));
            }
        }

        System.out.println("Welcome to the sudoku solver!");
        System.out.println("Enter the initial grid, and then enter a blank line to solve");
        int[][] initialGrid = new int[10][10];
        Scanner sc = new Scanner(System.in);
        // Input the initial grid
        while(true){
            System.out.print("Enter a row index from 1-9 (or enter to continue): ");
            String row = sc.nextLine();
            if(row.length() == 0) break;
            System.out.print("Enter a column index from 1-9: ");
            String col = sc.nextLine();
            System.out.print("Enter a value from 1-9: ");
            String num = sc.nextLine();

            initialGrid[Integer.parseInt(row)][Integer.parseInt(col)] = Integer.parseInt(num);
        }

        // Add an axiom for each entry of the initial grid
        for(int r = 1; r <= 9; ++r){
            for(int c = 1; c <= 9; ++c){
                if(initialGrid[r][c] != 0){
                    axioms.add(mkEq(
                        mkApp(entry, digits[r], digits[c]),
                        digits[initialGrid[r][c]]
                    ));
                }
            }
        }

        // Initialize the theory
        Theory sudokuTheory =  Theory.empty()
            .withSorts(Digit)
            .withFunctionDeclarations(entryFn)
            .withAxioms(axioms);

        // Initialize a model finder
        ModelFinder finder = ModelFinder.createDefault();

        // Set the theory of the model finder
        finder.setTheory(sudokuTheory);

        // Set the scopes of the model finder
        finder.setAnalysisScope(Digit, 9);

        System.out.println("Searching for a solution to the following sudoku:");
        printSudoku(initialGrid);
        System.out.println("...\n");

        // Check if all axioms in the theory are satisfiable
        ModelFinderResult result = finder.checkSat();

        // Print out model if it exists
        if(result.equals(ModelFinderResult.Sat())) {
            System.out.println("Solution found!\n");
            // Get the definition of the function back from the model finder
            Map<List<Value>, Value> resultMap = finder.viewModel().functionInterpretationsJava().get(entryFn);
            int[][] solvedSudoku = new int[10][10];
            // Map the entries function to a grid that can be displayed to the user
            for(int r = 1; r <= 9; ++r){
                for(int c = 1; c <= 9; ++c){
                    List<Value> position = new ArrayList<>(2);
                    position.add((Value)digits[r]);
                    position.add((Value)digits[c]);
                    solvedSudoku[r][c] = digitIntegers.get(resultMap.get(position));
                }
            }
            printSudoku(solvedSudoku);
        }
        else if(result.equals(ModelFinderResult.Unsat())){
            System.out.println("No solutions exist");
        }
        else {
            System.out.println("No solutions found");
        }
    }
}
