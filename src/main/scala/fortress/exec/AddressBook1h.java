package fortress.exec;

import fortress.msfol.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

public final class AddressBook1h {

	public static void main(String[] args) throws Exception {

		Theory theory = Theory.empty();
		Sort name = Sort.mkSortConst("Name");
		theory = theory.withSort(name);

		Sort addr = Sort.mkSortConst("Addr");
		theory = theory.withSort(addr);

		Sort book = Sort.mkSortConst("Book");
		theory = theory.withSort(book);

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("addr", book, name, addr, Sort.Bool()));

		Var b = Term.mkVar("b");
		Var n = Term.mkVar("n");
		Var a = Term.mkVar("a");
		Var a2 = Term.mkVar("a'");
		theory = theory.withAxiom(Term.mkForall(List.of(b.of(book), n.of(name), a.of(addr)), Term.mkImp(Term.mkApp("addr", b, n, a), Term.mkForall(a2.of(addr), Term.mkImp(Term.mkApp("addr", b, n, a2), Term.mkEq(a, a2))))));

		Var b2 = Term.mkVar("b'");
		Var b3 = Term.mkVar("b''");
		Var n2 = Term.mkVar("n'");

		Term t1 = Term.mkForall(a2.of(addr), Term.mkNot(Term.mkApp("addr", b, n, a2)));
		Term t2 = Term.mkForall(List.of(n2.of(name), a2.of(addr)), Term.mkIff(Term.mkApp("addr", b2, n2, a2), Term.mkOr(Term.mkApp("addr", b, n2, a2), Term.mkAnd(Term.mkEq(n2, n), Term.mkEq(a2, a)))));
		Term t3 = Term.mkForall(List.of(n2.of(name), a2.of(addr)), Term.mkIff(Term.mkApp("addr", b3, n2, a2), Term.mkAnd(Term.mkApp("addr", b2, n2, a2), Term.mkNot(Term.mkEq(n2, n)))));
		Term t4 = Term.mkForall(List.of(n2.of(name), a2.of(addr)), Term.mkIff(Term.mkApp("addr", b, n2, a2), Term.mkApp("addr", b3, n2, a2)));
		theory = theory.withAxiom(Term.mkNot(Term.mkForall(List.of(b.of(book), b2.of(book), b3.of(book), n.of(name), a.of(addr)), Term.mkImp(Term.mkAnd(t1, t2, t3), t4))));

		ModelFinder finder = new FortressTWO();
		finder.setTheory(theory);
		finder.setAnalysisScope(name, 40);
		finder.setAnalysisScope(addr, 40);
		finder.setAnalysisScope(book, 40);
        finder.setTimeout(240000);
        try{
			Writer log = new OutputStreamWriter(System.out);
            finder.setOutput(log);
            // finder.setDebug(true);
			ModelFinderResult res = finder.checkSat();
			if (res.equals(ModelFinderResult.Sat())) { System.out.println(finder.viewModel()); }
		} catch (Exception e) { e.printStackTrace(); }
		System.out.println("*************************FINISH*****************************");
	}
}
