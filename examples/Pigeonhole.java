import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;
import fortress.inputs.*;
import fortress.compiler.*;
import fortress.transformers.*;
import fortress.operations.*;
import fortress.interpretation.*;

import java.util.List;
import java.util.Map;
import java.io.*;


public class Pigeonhole {
    public static void main(String[] args) throws IOException {
//        if(args.length < 2) {
//            System.err.println("Please include numPigeons and numHoles");
//            System.exit(1);
//        }
//        int numPigeons = Integer.parseInt(args[0]);
//        int numHoles = Integer.parseInt(args[1]);
        
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
        Var p = mkVar("p");
        Var c = mkVar("c");


        // Create axiom
        // "Each hole has at most one pigeon"
        Term axiom = mkForall(List.of(h.of(H), p1.of(P), p2.of(P)),
            mkImp(
                mkNot(mkEq(p1, p2)),
                mkOr(
                    mkNot(mkEq(mkApp("f", p1), h)),
                    mkNot(mkEq(mkApp("f", p2), h))
                )));

        Term axiom1 = mkExists(p.of(P), mkEq(mkApp("f", p), mkApp("f", c)));
                
        // Begin with the empty theory
        Theory theory =  Theory.empty()
        // Add sorts
            .withSorts(P, H)
            .withConstant(c.of(P))
        // Add declarations
            .withFunctionDeclarations(f)
        // Add constraints
            .withAxiom(axiom)
            .withAxiom(axiom1);


        // This is satisfiable if and only if numPigeons <= numHoles
            
        // Initialize a model finder
        try(ModelFinder finder = ModelFinder.createDefault()) {
            // Set the theory of the model finder
            finder.setTheory(theory);
            
            // Set the scopes of the model finder
            finder.setExactScope(P, 2);
            finder.setExactScope(H, 3);
            // Check if all axioms in the theory are satisfiable
            ModelFinderResult result = finder.checkSat();
            
//            System.out.println("numPigeons:  " + numPigeons);
//            System.out.println("numHoles:    " + numHoles);
            System.out.println("Satisiable?: " + result.toString());
            
            // Print out model if it exists
            if(result.equals(ModelFinderResult.Sat())) {
                Interpretation model = finder.viewModel();
                System.out.println(model);
                InterpretationVerifier verifier = new InterpretationVerifier(theory);
                Boolean vResult = verifier.verifyInterpretation(model);
                System.out.println("If the interpretation satisfy the theory: " + vResult);
            }
        }
    }
}
