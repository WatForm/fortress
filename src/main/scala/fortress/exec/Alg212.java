package fortress.exec;

import fortress.msfol.*;
import static fortress.msfol.Term.*;
import static fortress.msfol.FuncDecl.*;
import static fortress.msfol.Sort.*;
import fortress.modelfind.*;
import fortress.transformers.*;

import java.io.*;
import java.util.List;
import java.util.Map;

// A fortress implementation of TPTP problem ALG212+1.p
// TPTP version 7.2.0
public class Alg212 {
    
    public static void main(String[] args) throws Exception {
        Sort Univ = mkSortConst("Univ");
        FuncDecl f = FuncDecl.mkFuncDecl("f", Univ, Univ, Univ, Univ);
        
        Var U = mkVar("U");
        Var W = mkVar("W");
        Var X = mkVar("X");
        Var Y = mkVar("Y");
        Var Z = mkVar("Z");
        
        Term majorityAxiom = Term.mkForall(List.of(X.of(Univ), Y.of(Univ)),
            Term.mkEq(Term.mkApp("f", X, X, Y), X));
        
        Term permute1Axiom = Term.mkForall(List.of(X.of(Univ), Y.of(Univ), Z.of(Univ)),
            Term.mkEq(Term.mkApp("f", X, Y, Z), Term.mkApp("f", Z, X, Y)));
        
        Term permute2Axiom = Term.mkForall(List.of(X.of(Univ), Y.of(Univ), Z.of(Univ)),
            Term.mkEq(Term.mkApp("f", X, Y, Z), Term.mkApp("f", X, Z, Y)));
        
        Term associativityAxiom = Term.mkForall(List.of(W.of(Univ), X.of(Univ), Y.of(Univ), Z.of(Univ)),
            Term.mkEq(Term.mkApp("f", Term.mkApp("f", X, W, Y), W, Z), Term.mkApp("f", X, W, Term.mkApp("f", Y, W, Z) )));
        
        Term dist_longConjecture = Term.mkForall(List.of(U.of(Univ), W.of(Univ), X.of(Univ), Y.of(Univ), Z.of(Univ)),
            Term.mkEq(
                Term.mkApp("f", Term.mkApp("f", X, Y, Z), U, W),
                Term.mkApp("f", Term.mkApp("f", X, U, W), Term.mkApp("f", Y, U, W), Term.mkApp("f", Z, U, W))));
        
        Theory theory = Theory.empty()
            .withSort(Univ)
            .withFunctionDeclaration(f)
            .withAxiom(majorityAxiom)
            .withAxiom(permute1Axiom)
            .withAxiom(permute2Axiom)
            .withAxiom(associativityAxiom)
            .withAxiom(mkNot(dist_longConjecture));
        
        ModelFinder finder = new FortressTWO();
		finder.setTheory(theory);
		finder.setAnalysisScope(Univ, 10);
        finder.setTimeout(1000000);
		try{
			Writer log = new OutputStreamWriter(System.out);
            finder.setOutput(log);
            // finder.setDebug(true);
			ModelFinderResult res = finder.checkSat();
			if (res.equals(ModelFinderResult.Sat())) { System.out.println(finder.viewModel()); }
		} catch (Exception e) { e.printStackTrace(); }
		System.out.println("*************************FINISH*****************************");
        
        // ModelFinder modelfinder = ModelFinder.createDefault();
        // modelfinder.setTimeout(2000);
        // modelfinder.setTheory(theory);
        // 
        // ModelFinderResult result;
        // if(printout) {
        //     Writer log = new PrintWriter(System.out);
        //     modelfinder.setOutput(log);
        // }
        // result = modelfinder.checkSat();
        // 
        // System.out.println();
        // System.out.println(result);
    }
}
