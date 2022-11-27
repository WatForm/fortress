import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

// This example is taken from "Finding Finite Models in Multi-sorted First-Order Logic"
// by Reger, Suda, and Voronkov

public class MonkeyVillage {
    public static void main(String[] args) throws IOException {
        if(args.length < 3) {
            System.err.println("Please include numTrees, numMonkeys, and numBananas");
            System.exit(1);
        }
        int numTrees = Integer.parseInt(args[0]);
        int numMonkeys = Integer.parseInt(args[1]);
        int numBananas = Integer.parseInt(args[2]);
        
        // Create Sorts
        Sort Tree = Sort.mkSortConst("Tree"); // Trees
        Sort Monkey = Sort.mkSortConst("Monkey"); // Monkeys
        Sort Banana = Sort.mkSortConst("Banana"); // Bananas
        
        // Create declarations
        // Relation which associates monkeys and bananas
        FuncDecl owns = FuncDecl.mkFuncDecl("owns", Monkey, Banana, Sort.Bool());
        // Functions that witness the monkeys' two bananas
        FuncDecl b1 = FuncDecl.mkFuncDecl("b1", Monkey, Banana);
        FuncDecl b2 = FuncDecl.mkFuncDecl("b2", Monkey, Banana);
        // Function that maps monkeys to the tree they sit in
        FuncDecl sits = FuncDecl.mkFuncDecl("sits", Monkey, Tree);
        // Function that associates each monkey with a partner
        FuncDecl partner = FuncDecl.mkFuncDecl("partner", Monkey, Monkey);
        
        
        // Create variables to use in axioms
        Var M = mkVar("M");
        Var M1 = mkVar("M1");
        Var M2 = mkVar("M2");
        Var M3 = mkVar("M3");
        Var M4 = mkVar("M4");
        Var B = mkVar("B");
        Var T = mkVar("T");
        
        // Create axiom
        // "Each monkey owns its two bananas, and those bananas are different"
        Term ax1 = mkForall(M.of(Monkey), mkAnd(
            mkApp("owns", M, mkApp("b1", M)),
            mkApp("owns", M, mkApp("b2", M)),
            mkNot(mkEq(mkApp("b1", M), mkApp("b2", M)))));
        // "Different monkeys don't own the same bananas"
        Term ax2 = mkForall(List.of(M1.of(Monkey), M2.of(Monkey), B.of(Banana)),
            mkImp(
                mkAnd(mkApp("owns", M1, B), mkApp("owns", M2, B)),
                mkEq(M1, M2)));
        // Each tree contains exactly three monkeys
        Term ax3 = mkForall(T.of(Tree), mkExists(List.of(M1.of(Monkey), M2.of(Monkey), M3.of(Monkey)),
            mkAnd(
                mkEq(mkApp("sits", M1), T),
                mkEq(mkApp("sits", M2), T),
                mkEq(mkApp("sits", M3), T),
                mkDistinct(M1, M2, M3))));
        Term ax4 = mkForall(List.of(M1.of(Monkey), M2.of(Monkey), M3.of(Monkey), M4.of(Monkey), T.of(Tree)),
            mkImp(
                mkAnd(
                    mkEq(mkApp("sits", M1), T),
                    mkEq(mkApp("sits", M2), T),
                    mkEq(mkApp("sits", M3), T),
                    mkEq(mkApp("sits", M4), T)
                ),
                mkNot(mkDistinct(M1, M2, M3, M4))));
        // No monkey is its own partner, and partners are paired up
        Term ax5 = mkForall(M.of(Monkey), mkAnd(
            mkNot(mkEq(mkApp("partner", M), M)),
            mkEq(mkApp("partner", mkApp("partner", M)), M)));
                
        // Begin with the empty theory
        Theory monkeyTheory =  Theory.empty()
        // Add sorts
            .withSorts(Tree, Monkey, Banana)
        // Add declarations
            .withFunctionDeclarations(owns, b1, b2, sits, partner)
        // Add constraints
            .withAxiom(ax1)
            .withAxiom(ax2)
            .withAxiom(ax3)
            .withAxiom(ax4)
            .withAxiom(ax5);
            
        // This is satisfiable if and only if numPigeons <= numHoles
            
        // Initialize a model finder
        try(ModelFinder finder = ModelFinder.createDefault()){
            // Set the theory of the model finder
            finder.setTheory(monkeyTheory);
            
            // Set the scopes of the model finder
//            finder.setExactScope(Tree, numTrees);
//            finder.setExactScope(Monkey, numMonkeys);
//            finder.setExactScope(Banana, numBananas);
            
            // Check if all axioms in the theory are satisfiable
            ModelFinderResult result = finder.checkSat();
            
            System.out.println("numTrees:   " + numTrees);
            System.out.println("numMonkeys: " + numMonkeys);
            System.out.println("numBananas: " + numBananas);
            System.out.println("Satisiable?: " + result.toString());
            
            // Print out model if it exists
            if(result.equals(ModelFinderResult.Sat())) {
                System.out.println(finder.viewModel());
            }
        }
    }
}
