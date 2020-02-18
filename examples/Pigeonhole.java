import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

public class Pigeonhole {
    public static void main(String[] args) {
        if(args.length < 2) {
            System.err.println("Please include numPigeons and numHoles");
            System.exit(1);
        }
        int numPigeons = Integer.parseInt(args[0]);
        int numHoles = Integer.parseInt(args[1]);
        
        // Create Sorts
        Sort P = Sort.mkSortConst("P"); // Pigeons
        Sort H = Sort.mkSortConst("H"); // Holes
        
        // Create declaration for hole assignment assignment function
        // f: P -> H
        FuncDecl f = FuncDecl.mkFuncDecl("f", P, H);
        
        // Create variables to use in axioms
        Var h = mkVar("h");
        Var p1 = mkVar("p1");
        Var p2 = mkVar("p2");
        
        // Create axiom
        // "Each hole has at most one pigeon"
        Term axiom = mkForall(List.of(h.of(H), p1.of(P), p2.of(P)),
            mkImp(
                mkNot(mkEq(p1, p2)),
                mkOr(
                    mkNot(mkEq(mkApp("f", p1), h)),
                    mkNot(mkEq(mkApp("f", p2), h))
                )));
                
        // Begin with the empty theory
        Theory pigeonholeTheory =  Theory.empty()
        // Add sorts
            .withSorts(P, H)
        // Add declarations
            .withFunctionDeclarations(f)
        // Add constraints
            .withAxiom(axiom);
            
        // This is satisfiable if and only if numPigeons <= numHoles
            
        // Initialize a model finder 
        ModelFinder finder = ModelFinder.createDefault();
        
        // Set the theory of the model finder
        finder.setTheory(pigeonholeTheory);
        
        // Set the scopes of the model finder
        finder.setAnalysisScope(P, numPigeons);
        finder.setAnalysisScope(H, numHoles);
        
        // Check if all axioms in the theory are satisfiable 
        ModelFinderResult result = finder.checkSat();
        
        System.out.println("numPigeons:  " + numPigeons);
        System.out.println("numHoles:    " + numHoles);
        System.out.println("satisiable?: " + result.toString());
    }
}