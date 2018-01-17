/*
 * Copyright (c) 2016, Amirhossein Vakili
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *    1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 *    2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package fortress.examples;

import fortress.fol.FOL;
import fortress.fol.finite_scope_solver.UIFSolver;
import fortress.fol.pterm.PTerm;
import fortress.lambda.Var;
import fortress.theory.Theory;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by Amirhossein Vakili.
 */
public final class FunctionVsRelation {

    private static boolean listsRel(int n){
        Theory result = new Theory("ListsUntyped", Theory.ARITH_THEORY);
        PTerm TElement = FOL.mkSort("TElement");
        PTerm TList = FOL.mkSort("TList");
        result.addCon(FOL.mkFun("element", TList, TElement, FOL.bool));
        result.addCon(FOL.mkFun("rest", TList, TList, FOL.bool));
        result.addAxiom("forall[l: TList. exists[ll: TList. rest[l, ll]]]");
        result.addAxiom("forall[l: TList. exists[e: TElement. element[l, e]]]");
        result.addAxiom("forall[l: TList, e1: TElement, e2: TElement. e1 = e2 | !element[l, e1] | !element[l, e2]]");
        result.addAxiom("forall[l: TList, l1: TList, l2: TList. l1 = l2 | !rest[l, l1] | !rest[l, l2]]");
        result.addAxiom("forall[l: TList, e: TElement. exists[ll: TList. rest[ll, l] & element[ll, e]]]");
        UIFSolver solver = new UIFSolver(result);
        Map<PTerm, Integer> bounds = new HashMap<>();
        bounds.put(TElement, n);
        bounds.put(TList, n);
        solver.verbosity = 1;
        solver.setUniverseByBounds(bounds);
        return solver.checkSat(true, false);
    }

    private static boolean listFun(int n){
        Theory result = new Theory("ListsUntyped", Theory.ARITH_THEORY);
        PTerm TElement = FOL.mkSort("TElement");
        PTerm TList = FOL.mkSort("TList");
        result.addCon(FOL.mkFun("element", TList, TElement));
        result.addCon(FOL.mkFun("rest", TList, TList));
        result.addAxiom("forall[l: TList, e: TElement. exists[ll: TList. rest[ll] = l & element[ll] = e]]");
        UIFSolver solver = new UIFSolver(result);
        Map<PTerm, Integer> bounds = new HashMap<>();
        bounds.put(TElement, n);
        bounds.put(TList, n);
        solver.verbosity = 1;
        solver.setUniverseByBounds(bounds);
        return solver.checkSat(true, false);
    }

    private static void medfun(int n){
        Theory spec = new Theory("MED009FUN", Theory.ARITH_THEORY);

        PTerm Univ = FOL.mkSort("Univ");
        PTerm BCapacity = FOL.mkSort("BCapacity");
        PTerm Condition = FOL.mkSort("Condition");
        PTerm Step = FOL.mkSort("Step");
        //PTerm Choice = FOL.mkSort("Choice");

        //declarations
        spec.addCon(FOL.mkFun("gt", Univ, Univ, FOL.bool));
        spec.addCon(FOL.mkFun("drugi", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("drugsu", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("drugbg", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("uptakelg", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("uptakepg", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("releaselg", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("bsecretioni", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("qilt27", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("sch1", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("sch2", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("sch3", Univ, FOL.bool));
        spec.addCon(FOL.mkFun("sch4", Univ, FOL.bool));

        // values
        spec.addCon(FOL.mkFun("NE", BCapacity));
        spec.addCon(FOL.mkFun("EX", BCapacity));
        spec.addCon(FOL.mkFun("SN", BCapacity));
        spec.addAxiom("NE != EX");
        spec.addAxiom("NE != SN");
        spec.addAxiom("EX != SN");

        spec.addCon(FOL.mkFun("bcapacity", Univ, BCapacity));


        spec.addCon(FOL.mkFun("HYPER", Condition));
        spec.addCon(FOL.mkFun("HYPO", Condition));
        spec.addCon(FOL.mkFun("NORMO", Condition));
        spec.addAxiom("HYPER != HYPO");
        spec.addAxiom("HYPER != NORMO");
        spec.addAxiom("HYPO != NORMO");

        spec.addCon(FOL.mkFun("condition", Univ, Condition));

        spec.addCon(FOL.mkFun("S0", Step));
        spec.addCon(FOL.mkFun("S1", Step));
        spec.addCon(FOL.mkFun("S2", Step));
        spec.addCon(FOL.mkFun("S3", Step));
        spec.addAxiom("S0 != S1");
        spec.addAxiom("S0 != S2");
        spec.addAxiom("S0 != S3");
        spec.addAxiom("S1 != S2");
        spec.addAxiom("S1 != S3");
        spec.addAxiom("S2 != S3");

        spec.addCon(FOL.mkFun("step", Univ, Step));

        spec.addAxiom("forall[x: Univ. !gt[x, x]]");
        spec.addAxiom("forall[x: Univ, y: Univ, z: Univ. gt[x, y] & gt[y, z] => gt[x, z]]");
        // insuline_effect
        spec.addAxiom("    forall[X0 : Univ.\n" +
                "      ( forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => drugi[X1] )]\n" +
                "     => forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => ( uptakelg[X1]\n" +
                "            & uptakepg[X1] ) )] )]\n");

        spec.addAxiom("forall[x0: Univ, x1: Univ. gt[x0, x1] | !uptakelg[x1] | !releaselg[x1]] ");
        // sulfony
        spec.addAxiom("   forall[X0 : Univ.\n" +
                "      ( ( forall[X1 : Univ.\n" +
                "            ( !gt[X0,X1]\n" +
                "           => drugsu[X1] )]\n" +
                "        & bcapacity[X0] != EX )\n" +
                "     => forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => bsecretioni[X1] )] )]");

        //biguani
        spec.addAxiom("    forall[X0 : Univ.\n" +
                "      ( forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => drugbg[X1] )]\n" +
                "     => forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => ! releaselg[X1] )] )]\n");
        //sn_cure_1
        spec.addAxiom("     forall[X0 : Univ.\n" +
                "      ( ( forall[X1 : Univ.\n" +
                "            ( !gt[X0,X1]\n" +
                "           => bsecretioni[X1] )]\n" +
                "        & bcapacity[X0] = SN\n" +
                "        & qilt27[X0]\n" +
                "        & forall[X1 : Univ.\n" +
                "            ( gt[X0,X1]\n" +
                "           => condition[X1] = HYPER )] )\n" +
                "     => forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => condition[X1] = NORMO )] )]");

        //sn_cure_2
        spec.addAxiom("     forall[X0 : Univ.\n" +
                "      ( ( forall[X1 : Univ.\n" +
                "            ( !gt[X0,X1]\n" +
                "           => !releaselg[X1] )]\n" +
                "        & bcapacity[X0] = SN\n" +
                "        & !qilt27[X0]\n" +
                "        & forall[X1 : Univ.\n" +
                "            ( gt[X0,X1]\n" +
                "           => condition[X1] = HYPER )] )\n" +
                "     => forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => condition[X1] = NORMO )] )]");
        //ne_cure_axiom
        spec.addAxiom("    forall[X0 : Univ.\n" +
                "      ( ( ( forall[X1 : Univ.\n" +
                "              ( !gt[X0,X1]\n" +
                "             => !releaselg[X1] )]\n" +
                "          | forall[X1 : Univ.\n" +
                "              ( !gt[X0,X1]\n" +
                "             => uptakepg[X1] )] )\n" +
                "        & bcapacity[X0] = NE\n" +
                "        & forall[X1 : Univ.\n" +
                "            ( !gt[X0,X1]\n" +
                "           => bsecretioni[X1] )]\n" +
                "        & forall[X1 : Univ.\n" +
                "            ( gt[X0,X1]\n" +
                "           => condition[X1] = HYPER )] )\n" +
                "     => forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => condition[X1] = NORMO )] )]");

        //ex_cure
        spec.addAxiom("    forall[X0 : Univ.\n" +
                "      ( ( forall[X1 : Univ.\n" +
                "            ( !gt[X0,X1]\n" +
                "           => uptakelg[X1] )]\n" +
                "        & forall[X1 : Univ.\n" +
                "            ( !gt[X0,X1]\n" +
                "           => uptakepg[X1] )]\n" +
                "        & bcapacity[X0] = NE\n" +
                "        & forall[X1 : Univ.\n" +
                "            ( gt[X0,X1]\n" +
                "           => condition[X1]= HYPER )] )\n" +
                "     => forall[X1 : Univ.\n" +
                "          ( ! gt[X0,X1]\n" +
                "         => ( condition[X1]= NORMO\n" +
                "            | condition[X1] = HYPO ) )] )]");

        //normo1
        spec.addAxiom(" forall[X0: Univ. ((sch1[X0]) =>\n" +
                "(!\n" +
                "(forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => condition[X1] = NORMO )])\n" +
                ")\n" +
                ")]\n");
        //normo2
        spec.addAxiom("forall[X0: Univ. (((!sch1[X0]) & sch2[X0]) =>\n" +
                "( forall[X1 : Univ.\n" +
                "              ( ! gt[X0,X1]\n" +
                "             => bsecretioni[X1] )]\n" +
                "          & bcapacity[X0] = SN\n" +
                "          & qilt27[X0]\n" +
                "          & forall[X1 : Univ.\n" +
                "              ( gt[X0,X1]\n" +
                "             => condition[X1] = HYPER )] ))]\n");
        // normo3
        spec.addAxiom("forall[X0: Univ. (((!sch1[X]) & (!sch2[X0]) & sch3[X0]) =>   \n" +
                "( forall[X1 : Univ.\n" +
                "              ( !gt[X0,X1]\n" +
                "             => !releaselg[X1] )]\n" +
                "          & bcapacity[X0] = SN\n" +
                "          & !qilt27[X0]\n" +
                "          & forall[X1 : Univ.\n" +
                "              ( gt[X0,X1]\n" +
                "             => condition[X1] = HYPER )] )\n" +
                ")]\n");

        //normo4
        spec.addAxiom("forall[X0: Univ. (((!sch1[X0]) & (!sch2[X0]) & (!sch3[X0]) & sch4[X0]) =>\n" +
                "( ( forall[X1 : Univ.\n" +
                "                ( ! gt[X0,X1]\n" +
                "               => !releaselg[X1] )]\n" +
                "            | forall[X1 : Univ.\n" +
                "                ( !gt[X0,X1]\n" +
                "               => uptakepg[X1] )] )\n" +
                "          & bcapacity[X0] = NE\n" +
                "          & forall[X1 : Univ.\n" +
                "              ( !gt[X0,X1]\n" +
                "             => bsecretioni[X1] )]\n" +
                "          & forall[X1 : Univ.\n" +
                "              ( gt[X0,X1]\n" +
                "             => condition[X1] = HYPER )] ))]");

        //normo5
        spec.addAxiom("forall[X0: Univ. (((!sch1[X0]) & (!sch2[X0]) & (!sch3[X0]) & (!sch4[X0])) =>\n" +
                "( forall[X1 : Univ.\n" +
                "              ( !gt[X0,X1]\n" +
                "             => uptakelg[X1] )]\n" +
                "          & forall[X1 : Univ.\n" +
                "              ( !gt[X0,X1]\n" +
                "             => uptakepg[X1] )]\n" +
                "          & bcapacity[X0] =EX\n" +
                "          & forall[X1 : Univ.\n" +
                "              ( gt[X0,X1]\n" +
                "             => condition[X1] = HYPER )] ))]\n");
        //step1
        spec.addAxiom("forall[X0 : Univ.\n" +
                "      ( ( step[X0] =S1\n" +
                "        & qilt27[X0] )\n" +
                "     => drugsu[X0] )]");

        //step2
        spec.addAxiom("forall[X0 : Univ.\n" +
                "      ( ( step[X0] = S1\n" +
                "        & !qilt27[X0] )\n" +
                "     => drugbg[X0] )\n]");

        //step3
        spec.addAxiom("forall[X0 : Univ.\n" +
                "      ( step[X0] = S2\n" +
                "     => ( drugbg[X0]\n" +
                "        & drugsu[X0] ) )]\n");
        //step4
        spec.addAxiom("forall[X0 : Univ.\n" +
                "      ( step[X0] = S2\n" +
                "     => ( drugbg[X0]\n" +
                "        & drugsu[X0] ) )]\n");

        //bgcomp
        spec.addAxiom("forall[X0 : Univ.\n" +
                "      ( drugbg[X0]\n" +
                "     => ( ( step[X0] = S1\n" +
                "          & !qilt27[X0] )\n" +
                "        | step[X0] = S2\n" +
                "        | step[X0] = S3) )]\n");
        //sucomp
        spec.addAxiom("forall[X0 : Univ.\n" +
                "      ( drugsu[X0]\n" +
                "     => ( ( step[X0] = S1\n" +
                "          & !qilt27[X0] )\n" +
                "        | step[X0] = S2\n" +
                "        | step[X0] = S3) )]\n");

        //insulincomp
        spec.addAxiom("forall[X0: Univ. drugi[X0] => step[X0] = S3]");

        //insulin_completion
        spec.addAxiom("     forall[X0 : Univ.\n" +
                "       ( forall[X1 : Univ.\n" +
                "            ( !gt[X0,X1]\n" +
                "           => uptakelg[X1] )]\n" +
                "        | forall[X1 : Univ.\n" +
                "            ( !gt[X0,X1]\n" +
                "           => uptakepg[X1] )] )\n" +
                "     => forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => drugi[X1] )]]");
        //uptake completion
        spec.addAxiom("forall[X0 : Univ, X1 : Univ .\n" +
                "      ( !gt[X0,X1]\n" +
                "     => ( !releaselg[X1]\n" +
                "       => uptakelg[X1] ) )]\n");
        //su_completion
        spec.addAxiom("forall[X0 : Univ.\n" +
                "      ( forall[X1 : Univ.\n" +
                "          ( ! gt[X0,X1]\n" +
                "         => bsecretioni[X1] )]\n" +
                "     => ( forall[X1 : Univ.\n" +
                "            ( ! gt[X0,X1]\n" +
                "           => drugsu[X1] )]\n" +
                "        & bcapacity[X0] != EX ) )]");

        //bg_completion
        spec.addAxiom("     forall[X0 : Univ.\n" +
                "      ( forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => !releaselg[X1] )]\n" +
                "     => forall[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "         => drugbg[X1] )] )]\n");

        //trans_ax1
        spec.addAxiom("    forall[X0 : Univ.\n" +
                "      ( ( step[X0] = S0\n" +
                "        & ! forall[X1 : Univ.\n" +
                "              ( ! gt[X0,X1]\n" +
                "             => condition[X1] = NORMO)] )\n" +
                "     => exists[X1 : Univ.\n" +
                "          ( ! gt[X0,X1]\n" +
                "          & step[X1] = S1\n" +
                "          & forall[X2 : Univ.\n" +
                "              ( gt[X1,X2]\n" +
                "             => condition[X2] = HYPER )] )] )]\n");
        //trans_ax2
        spec.addAxiom(" forall[X0 : Univ.\n" +
                "      ( ( step[X0] = S1\n" +
                "        & !forall[X1 : Univ.\n" +
                "              ( ! gt[X0,X1]\n" +
                "             => condition[X1] = NORMO )] )\n" +
                "     => exists[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "          & step[X1] = S2\n" +
                "          & forall[X2 : Univ.\n" +
                "              ( gt[X1,X2]\n" +
                "             => condition[X2] = HYPER )]\n" +
                "          & ( bcapacity[X1] = NE\n" +
                "            | bcapacity[X1] = EX ) )] )]");
        //trans_ax3
        spec.addAxiom("      forall[X0 : Univ.\n" +
                "      ( ( step[X0] = S2\n" +
                "        & !forall[X1 : Univ.\n" +
                "              ( !gt[X0,X1]\n" +
                "             => condition[X1] = NORMO )] )\n" +
                "     => exists[X1 : Univ.\n" +
                "          ( !gt[X0,X1]\n" +
                "          & step[X1] = S3\n" +
                "          & forall[X2 : Univ.\n" +
                "              ( gt[X1,X2]\n" +
                "             => condition[X2] = HYPER )]\n" +
                "          & bcapacity[X1] = EX )] )]\n");

        //conjecture
        spec.addAxiom("!exists[n0: Univ. (step[n0] = S1\n" +
                "      & forall[X0 : Univ.\n" +
                "          ( gt[n0,X0]\n" +
                "         => condition[X0] = HYPER )]\n" +
                "      & ! bcapacity[n0] = SN\n" +
                "      & ! qilt27[n0] )\n" +
                "   => exists[X0 : Univ.\n" +
                "        ( !gt[n0,X0]\n" +
                "        & step[X0] = S2\n" +
                "        & forall[X1 : Univ.\n" +
                "            ( gt[X0,X1]\n" +
                "           => condition[X1] = HYPER )]\n" +
                "        & ( bcapacity[X0] = NE\n" +
                "          | bcapacity[X0] = EX ) )]]\n");
        //System.out.println(spec);
        UIFSolver solver = new UIFSolver(spec);
        Map<PTerm, Integer> bounds = new HashMap<>();
        bounds.put(Univ, n);
        bounds.put(BCapacity, 3);
        bounds.put(Step, 4);
        bounds.put(Condition, 3);
        //bounds.put(Choice, 5);
        solver.verbosity = 1;
        solver.setUniverseByBounds(bounds);
        solver.checkSat(true, false);
    }

    public static void main(String[] args) {
        if (args.length == 3){
            int n = Integer.parseInt(args[2]);
            boolean fun = args[1].equals("fun");
            switch (args[0]){
                case "list":
                    fun = fun ? listFun(n) : listsRel(n);
                    return;
                default:
                    System.out.println("Unknow case study.");
                    return;
            }
        } else {
            if (args.length == 1)
                medfun(Integer.parseInt(args[0]));
        }
        medfun(21);
    }
}
