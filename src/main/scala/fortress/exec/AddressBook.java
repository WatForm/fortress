package fortress.exec;

import fortress.msfol.*;
import fortress.modelfind.*;

import java.util.List;
import java.io.*;

public final class AddressBook {

	public static void main(String[] args) throws Exception {

		Theory theory = Theory.empty();
		Sort x2 = Sort.mkSortConst("sortthis/Name");
		theory = theory.withSort(x2);

		Sort x3 = Sort.mkSortConst("sortthis/Addr");
		theory = theory.withSort(x3);

		Sort x4 = Sort.mkSortConst("sortthis/Book");
		theory = theory.withSort(x4);

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("this/Name", x2, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("this/Addr", x3, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("this/Book", x4, Sort.Bool()));

		theory = theory.withFunctionDeclaration(FuncDecl.mkFuncDecl("this/Book.addr", x4, x2, x3, Sort.Bool()));

		Var x6 = Term.mkVar("var_3");
		Var x7 = Term.mkVar("var_4");
		Var x8 = Term.mkVar("var_5");
		Term x10 = Term.mkApp("this/Book.addr", x6, x7, x8);
		Term x13 = Term.mkApp("this/Book", x6);
		Term x14 = Term.mkApp("this/Name", x7);
		Term x12 = Term.mkAnd(x13, x14);
		Term x15 = Term.mkApp("this/Addr", x8);
		Term x11 = Term.mkAnd(x12, x15);
		Term x9 = Term.mkImp(x10, x11);
		Term x5 = Term.mkForall(List.of(x6.of(x4), x7.of(x2), x8.of(x3)), x9);
		theory = theory.withAxiom(x5);

		Var x17 = Term.mkVar("delUndoesAdd_this_0");
		Term x19 = Term.mkApp("this/Book", x17);
		Var x22 = Term.mkVar("var_10");
		Term x24 = Term.mkApp("this/Addr", x22);
		Var x26 = Term.mkVar("var_11");
		Term x28 = Term.mkApp("this/Book.addr", x17, x26, x22);
		Term x29 = Term.mkApp("this/Name", x26);
		Term x27 = Term.mkImp(x28, x29);
		Term x25 = Term.mkForall(List.of(x26.of(x2)), x27);
		Term x23 = Term.mkImp(x24, x25);
		Term x21 = Term.mkForall(List.of(x22.of(x3)), x23);
		Var x31 = Term.mkVar("var_6");
		Term x33 = Term.mkApp("this/Name", x31);
		Var x36 = Term.mkVar("var_7");
		Term x38 = Term.mkApp("this/Book.addr", x17, x31, x36);
		Term x39 = Term.mkApp("this/Addr", x36);
		Term x37 = Term.mkImp(x38, x39);
		Term x35 = Term.mkForall(List.of(x36.of(x3)), x37);
		Var x41 = Term.mkVar("var_9");
		Term x43 = Term.mkApp("this/Book.addr", x17, x31, x41);
		Var x45 = Term.mkVar("var_8");
		Term x47 = Term.mkApp("this/Book.addr", x17, x31, x45);
		Term x48 = Term.mkEq(x45, x41);
		Term x46 = Term.mkImp(x47, x48);
		Term x44 = Term.mkForall(List.of(x45.of(x3)), x46);
		Term x42 = Term.mkImp(x43, x44);
		Term x40 = Term.mkForall(List.of(x41.of(x3)), x42);
		Term x34 = Term.mkAnd(x35, x40);
		Term x32 = Term.mkImp(x33, x34);
		Term x30 = Term.mkForall(List.of(x31.of(x2)), x32);
		Term x20 = Term.mkAnd(x21, x30);
		Term x18 = Term.mkImp(x19, x20);
		Term x16 = Term.mkForall(List.of(x17.of(x4)), x18);
		theory = theory.withAxiom(x16);

		Var x51 = Term.mkVar("delUndoesAdd_b_0");
		Var x52 = Term.mkVar("delUndoesAdd_b'_0");
		Var x53 = Term.mkVar("delUndoesAdd_b''_0");
		Var x54 = Term.mkVar("delUndoesAdd_n_0");
		Var x55 = Term.mkVar("delUndoesAdd_a_0");
		Term x58 = Term.mkApp("this/Book", x51);
		Term x59 = Term.mkApp("this/Book", x52);
		Term x60 = Term.mkApp("this/Book", x53);
		Term x61 = Term.mkApp("this/Name", x54);
		Term x62 = Term.mkApp("this/Addr", x55);
		Term x57 = Term.mkAnd(x58, x59, x60, x61, x62);
		Var x68 = Term.mkVar("var_12");
		Term x70 = Term.mkApp("this/Book.addr", x51, x54, x68);
		Term x69 = Term.mkNot(x70);
		Term x67 = Term.mkForall(List.of(x68.of(x3)), x69);
		Var x72 = Term.mkVar("var_13");
		Var x73 = Term.mkVar("var_14");
		Term x75 = Term.mkApp("this/Book.addr", x52, x72, x73);
		Term x77 = Term.mkApp("this/Book.addr", x51, x72, x73);
		Term x79 = Term.mkEq(x72, x54);
		Term x80 = Term.mkEq(x73, x55);
		Term x78 = Term.mkAnd(x79, x80);
		Term x76 = Term.mkOr(x77, x78);
		Term x74 = Term.mkIff(x75, x76);
		Term x71 = Term.mkForall(List.of(x72.of(x2), x73.of(x3)), x74);
		Term x66 = Term.mkAnd(x67, x71);
		Var x82 = Term.mkVar("var_15");
		Var x83 = Term.mkVar("var_16");
		Term x85 = Term.mkApp("this/Book.addr", x53, x82, x83);
		Term x87 = Term.mkApp("this/Book.addr", x52, x82, x83);
		Term x90 = Term.mkEq(x82, x54);
		Term x91 = Term.mkApp("this/Addr", x83);
		Term x89 = Term.mkAnd(x90, x91);
		Term x88 = Term.mkNot(x89);
		Term x86 = Term.mkAnd(x87, x88);
		Term x84 = Term.mkIff(x85, x86);
		Term x81 = Term.mkForall(List.of(x82.of(x2), x83.of(x3)), x84);
		Term x65 = Term.mkAnd(x66, x81);
		Term x64 = Term.mkNot(x65);
		Var x93 = Term.mkVar("var_17");
		Var x94 = Term.mkVar("var_18");
		Term x96 = Term.mkApp("this/Book.addr", x51, x93, x94);
		Term x97 = Term.mkApp("this/Book.addr", x53, x93, x94);
		Term x95 = Term.mkIff(x96, x97);
		Term x92 = Term.mkForall(List.of(x93.of(x2), x94.of(x3)), x95);
		Term x63 = Term.mkOr(x64, x92);
		Term x56 = Term.mkImp(x57, x63);
		Term x50 = Term.mkForall(List.of(x51.of(x4), x52.of(x4), x53.of(x4), x54.of(x2), x55.of(x3)), x56);
		Term x49 = Term.mkNot(x50);
		theory = theory.withAxiom(x49);

		ModelFinder finder = new FortressTWO();
		finder.setTheory(theory);
		finder.setAnalysisScope(x2, 30);
		finder.setAnalysisScope(x3, 30);
		finder.setAnalysisScope(x4, 30);
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
