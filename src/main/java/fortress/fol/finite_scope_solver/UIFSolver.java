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

package fortress.fol.finite_scope_solver;

import fortress.fol.*;
import fortress.fol.pterm.PTerm;
import fortress.fol.visitor.FormulaFlattenTerm;
import fortress.lambda.Con;
import fortress.lambda.Term;
import fortress.lambda.Type;
import fortress.lambda.Var;
import fortress.lambda.visitor.MaxIDTerm;
import fortress.theory.Theory;
import fortress.formats.smt.smtlib.ComExpr;
import fortress.formats.smt.smtlib.SExpr;
import fortress.formats.smt.smtlib.StrExpr;
import fortress.util.Graph;
import fortress.util.Pair;
import fortress.util.Timer;

import java.io.*;
import java.util.*;
import java.util.function.Function;

import static fortress.util.Errors.failIf;

/**
 * Created by Amirhossein Vakili.
 */
public class UIFSolver {

    private Theory theory;
    private Map<PTerm, List<Con>> universe;
    private int universeSize;
    private Map<Term, Con> model;

    private List<SExpr> declarationList;
    private Set<SExpr> simpleGroundedFormulaList;
    private List<SExpr> generalGroundedFormulaList;
    private List<SExpr> getModelDeclarationList;

    private Map<String, Integer> maxIDs;
    private Map<Term, Formula> learnedLiterals;
    private List<Set<Term>> pairwiseDistinct;
    private List<Con> helperConstants;
    private List<Formula> FOLFormulas;

    // -1 means unsat, 0 means unknown, 1 means sat
    private int isSat;
    public int verbosity;
    public boolean flattenTerm;
    private boolean is_quantifier_free;

    public UIFSolver(Theory theory){
        this.theory = theory;
        is_quantifier_free = true;
        flattenTerm = false;
        universeSize = 0;
        isSat = 0;
        verbosity = 0;
        declarationList = new LinkedList<>();
        simpleGroundedFormulaList = new HashSet<>();
        generalGroundedFormulaList = new LinkedList<>();
        getModelDeclarationList = new LinkedList<>();
        maxIDs = new HashMap<>();
        learnedLiterals = new HashMap<>();
        helperConstants = new LinkedList<>();
        FOLFormulas = new LinkedList<>();
        translateSorts();
    }

    /*
    public UIFSolver(Theory theory, int verbosity){
        this.theory = theory;
        isSat = 0;
        this.verbosity = verbosity;
        declarationList = new LinkedList<>();
        simpleGroundedFormulaList = new TreeSet<>();
        generalGroundedFormulaList = new LinkedList<>();
        getModelDeclarationList = new LinkedList<>();
        learnedLiterals = new TreeMap<>();
        helperConstants = new LinkedList<>();
        FOLFormulas = new LinkedList<>();
    }
    */

    public Map<PTerm, List<Con>> getUniverse(){
        return universe;
    }

    public Map<Term, Con> getModel(){
        failIf(isSat <= 0);
        return model;
    }

    public void setPositiveInstances(Map<Term, Term> instances){
        for (Map.Entry<Term, Term> e: instances.entrySet()){
            Term t1 = e.getKey();
            Term t2 = e.getValue();
            int test = t1.compareTo(t2);
            if (test == 0)
                continue;
            if (test > 0) {
                Term temp = FOL.mkEq(t1, t2);
                learnedLiterals.put(temp, Formula.true_);
                simpleGroundedFormulaList.add(temp.toSMTLIB());
            }
            else{
                Term temp = FOL.mkEq(t2, t1);
                learnedLiterals.put(temp, Formula.true_);
                simpleGroundedFormulaList.add(temp.toSMTLIB());
            }
        }
    }

    public void setNegetativeInstances(Map<Term, Term> instances){
        for (Map.Entry<Term, Term> e: instances.entrySet()){
            Term t1 = e.getKey();
            Term t2 = e.getValue();
            int test = t1.compareTo(t2);
            if (test == 0){
                isSat = -1;
                return;
            }
            if (test > 0){
                Term temp = FOL.mkEq(t1, t2);
                learnedLiterals.put(temp, Formula.false_);
                simpleGroundedFormulaList.add(new Not(new Atomic(temp)).toSMTLIB());
            }
            else {
                Term temp = FOL.mkEq(t2, t1);
                learnedLiterals.put(temp, Formula.false_);
                simpleGroundedFormulaList.add(new Not(new Atomic(temp)).toSMTLIB());
            }

        }
    }

    private void computeMaxIds(){
        for (Pair<String, Integer> p: theory.functorSet)
            for (Term a: theory.axiomSet)
                maxIDs.put(p.left, maxIDs.getOrDefault(p.left, 0) + a.accept( new MaxIDTerm("_" + p.left)));
        for (Term a: theory.axiomSet) {
            maxIDs.put("_skolem", maxIDs.getOrDefault("_skolem", 0) + a.accept(new MaxIDTerm("_skolem")));
            maxIDs.put("ft", maxIDs.getOrDefault("ft", 0) + a.accept(new MaxIDTerm("TT")));
        }
    }

    private void normalizer(){
        computeMaxIds();
        if (theory.axiomSet.isEmpty())
            return;
        FormulaFlattenTerm fft = new FormulaFlattenTerm(maxIDs.get("ft"));
        for (Term a: theory.axiomSet){
            //System.out.print(a + " ==> ");
            Formula debug;
            if (flattenTerm)
                debug = Formula.fromTerm(a.distinctVar("v")).accept(fft).nnf().simplify().prenex();
            else
                debug = Formula.fromTerm(a.distinctVar("v")).nnf().simplify().prenex();
            final int currentIndex = maxIDs.get("_skolem");
            Pair<Formula, List<Con>> p = debug.skolemize(currentIndex);
            maxIDs.put("_skolem", currentIndex + p.right.size());
            helperConstants.addAll(p.right);
            debug = p.left.simplify();
            is_quantifier_free = is_quantifier_free && debug.is_quantifier_free();
            FOLFormulas.add(debug);
            //System.out.println(debug);
        }
    }

    private static SExpr mkAssert(SExpr s){
        return new ComExpr(new StrExpr("assert"), s);
    }

    private void setUniverse(Map<PTerm, List<Con>> universe){
        // normalize
        normalizer();
        this.universe = universe;
        // add universe to helperConstants
        // and update pairwiseDistinct
        // and add the distinct constraint to smtlib
        // and add declaration of universe to smtlib
        pairwiseDistinct = new LinkedList<>();
        if (verbosity > 0)
            System.out.println("Adding distinct constraints:");
        for (Map.Entry<PTerm, List<Con>> e: universe.entrySet()) {
            final int len = e.getValue().size();
            Set<Term> distinct = new TreeSet<>();
            List<SExpr> smtDistinct = new LinkedList<>();
            smtDistinct.add(new StrExpr("distinct"));
            universeSize += len;
            for (Con c: e.getValue()) {
                declarationList.add(new ComExpr(new StrExpr("declare-fun"),
                        new StrExpr(c.getName()),
                        new ComExpr(),
                        new StrExpr(e.getKey().toString())));
                getModelDeclarationList.add(new StrExpr(c.getName()));
                distinct.add(c);
                smtDistinct.add(new StrExpr(c.getName()));
            }
            pairwiseDistinct.add(distinct);
            generalGroundedFormulaList.add(mkAssert(new ComExpr(smtDistinct)));
        }
    }

    public void setUniverseByBounds(Map<PTerm, Integer> boundSizes){
        // normalize
        normalizer();
        if (is_quantifier_free)
            return;
        // add universe to helper constants
        // and update pairwiseDistinct
        // and add the distinct constraint to smtlib
        // and add declaration of universe to smtlib
        universe = new HashMap<>();
        pairwiseDistinct = new LinkedList<>();
        if (verbosity > 0)
            System.out.println("Adding distinct constraints:");
        for (Map.Entry<PTerm, Integer> e: boundSizes.entrySet()){
            universeSize += e.getValue();
            List<Con> l = new ArrayList<>(e.getValue());
            Set<Term> distinct = new TreeSet<>();
            List<SExpr> smtDistinct =  new LinkedList<>();
            smtDistinct.add(new StrExpr("distinct"));
            String typeName = e.getKey().toString();
            for (int i = 0; i != e.getValue(); i++) {
                final int currentIndex = maxIDs.get(typeName);
                String name = "_" + typeName + Integer.toString(currentIndex);
                maxIDs.put(typeName, currentIndex + 1);
                Con c = FOL.mkFun(name, e.getKey());
                declarationList.add(new ComExpr(new StrExpr("declare-fun"),
                        new StrExpr(name),
                        new ComExpr(),
                        new StrExpr(typeName)));
                getModelDeclarationList.add(new StrExpr(name));
                l.add(c);
                distinct.add(c);
                smtDistinct.add(new StrExpr(name));
            }
            universe.put(e.getKey(), l);
            pairwiseDistinct.add(distinct);
            generalGroundedFormulaList.add(mkAssert(new ComExpr(smtDistinct)));
        }
    }

    private void translateSorts(){
        for (Pair<String, Integer> p: theory.functorSet)
            declarationList.add(new ComExpr(new StrExpr("declare-sort"), new StrExpr(p.left), new StrExpr("0")));
    }

    private void translateConstants(){
        for (Con c: theory.constantSet){
            Pair<List<PTerm>, PTerm> p = Type.brkFnTys(c.getType());
            List<SExpr> temp = new ArrayList<>(p.left.size());
            for (PTerm pt: p.left)
                temp.add(new StrExpr(pt.toString()));
            declarationList.add(new ComExpr(new StrExpr("declare-fun"),
                    new StrExpr(c.getName()),
                    new ComExpr(temp),
                    new StrExpr(p.right.toString())));
        }
        for (Con c: helperConstants){
            Pair<List<PTerm>, PTerm> p = Type.brkFnTys(c.getType());
            List<SExpr> temp = new ArrayList<>(p.left.size());
            for (PTerm pt: p.left)
                temp.add(new StrExpr(pt.toString()));
            declarationList.add(new ComExpr(new StrExpr("declare-fun"),
                    new StrExpr(c.getName()),
                    new ComExpr(temp),
                    new StrExpr(p.right.toString())));
        }
    }

    private void translateDefinitions(){
        for (String defname: theory.defSetOrder)
            declarationList.add(theory.defSet.get(defname).toSMTLIB());
    }

    private void generateRangeConstraints(boolean symmetry){
        if (symmetry){
            List<PTerm> vertex = new LinkedList<>();
            vertex.addAll(universe.keySet());
            Graph<PTerm, Con> graph = new Graph<>(vertex);
            for (Con c: theory.constantSet){
                Pair<List<PTerm>, PTerm> p = Type.brkFnTys(c.getType());
                Pair<String, Integer> pt = new Pair<>(p.right.toString(), 0);
                if (theory.isInBase(pt))
                    continue;
                for (PTerm v1: p.left)
                    if (!v1.equals(p.right)) {
                        graph.addEdge(v1, p.right, c);
                    }
            }
            for (Con c: helperConstants){
                Pair<List<PTerm>, PTerm> p = Type.brkFnTys(c.getType());
                for (PTerm v1: p.left)
                    if (!v1.equals(p.right))
                        graph.addEdge(v1, p.right, c);
            }
            graph.uniquePaths();
            Function<PTerm, Comparator<Con>> mkComparator = (p) -> {
                Comparator<Con> sortConstants = (c1, c2) -> {
                    boolean f1 = graph.isOnCycle(c1);
                    boolean f2 = graph.isOnCycle(c2);
                    if (f1 && f2)
                        return c1.compareTo(c2);
                    if (f1)
                        return 1;
                    if (f2)
                        return -1;
                    Pair<List<PTerm>, PTerm> p1 = Type.brkFnTys(c1.getType());
                    Pair<List<PTerm>, PTerm> p2 = Type.brkFnTys(c2.getType());
                    int n1 = 0;
                    int n2 = 0;
                    for (PTerm pt: p1.left)
                        if (pt.equals(p))
                            n1++;
                    for (PTerm pt: p2.left)
                        if (pt.equals(p))
                            n2++;
                    int test = n1 - n2;
                    if (test != 0)
                        return test;
                    test = p1.left.size() - p2.left.size();
                    if (test != 0)
                        return test;
                    return c1.compareTo(c2);
                };
                return sortConstants;
            };
            for (Map.Entry<PTerm, List<Con>> e: universe.entrySet()){
                final int len = e.getValue().size();
                SortedSet<Con> sc = new TreeSet<>(mkComparator.apply(e.getKey()));
                for (Con c: theory.constantSet)
                    if (Type.isOutputType(c, e.getKey()))
                        sc.add(c);
                for (Con c: helperConstants)
                    if (Type.isOutputType(c, e.getKey()))
                        sc.add(c);
                int include = 1;
                for (Con c: sc){
                    if (graph.isOnCycle(c))
                        include = len;
                    Pair<List<PTerm>, PTerm> p = Type.brkFnTys(c.getType());
                    if (p.left.isEmpty()){
                        if (theory.constantSet.contains(c))
                            getModelDeclarationList.add(new StrExpr(c.getName()));
                        if (include != 1){
                            SortedSet<Formula> orArg = new TreeSet<>();
                            for (int i = 0; i != include; i++) {
                                if (c.compareTo(e.getValue().get(i)) > 0)
                                    orArg.add(new Atomic(FOL.mkEq(c, e.getValue().get(i))));
                                else
                                    orArg.add(new Atomic(FOL.mkEq(e.getValue().get(i), c)));
                            }
                            generalGroundedFormulaList.add(mkAssert(new Or(orArg).toSMTLIB()));
                        } else {
                            if (c.compareTo(e.getValue().get(0)) > 0)
                                simpleGroundedFormulaList.add(mkAssert(new Atomic(FOL.mkEq(c, e.getValue().get(0))).toSMTLIB()));
                            else
                                simpleGroundedFormulaList.add(mkAssert(new Atomic(FOL.mkEq(e.getValue().get(0), c)).toSMTLIB()));
                        }
                        include = Math.min(include + 1, len);
                    } else {
                        boolean flag = false;
                        if (p.left.contains(p.right)) {
                            include = Math.max(2, include);
                            flag = true;
                        }
                        flag = flag && (include != len);
                        int [] bounds = new int[p.left.size()];
                        PTerm [] typeList = new PTerm[bounds.length];
                        int i = 0;
                        for (PTerm pty: p.left) {
                            bounds[i] = universe.get(pty).size();
                            typeList[i++] = pty;
                        }
                        Counter counter = new Counter(bounds);
                        ArrayList<Term> args = new ArrayList<>(bounds.length);
                        for (i = 0; i!= bounds.length; i++)
                            args.add(null);
                        if (flag){
                            //take care of diagonal;
                            int j = 0;
                            if (verbosity > 0)
                                System.out.println("Applying diagonal XLNH:");
                            final int jlen =universe.get(p.right).size();
                            while (j < jlen){
                                Con temp = universe.get(p.right).get(j);
                                for (i = 0; i != bounds.length; i++)
                                    args.set(i, typeList[i].equals(p.right)? temp : universe.get(typeList[i]).get(0));
                                Term ft = FOL.apply(c, args);
                                if (theory.constantSet.contains(c))
                                    getModelDeclarationList.add(ft.toSMTLIB());
                                SortedSet<Formula> orArg = new TreeSet<>();
                                for (i = 0; i != include; i++) {
                                    if (ft.compareTo(e.getValue().get(i)) > 0)
                                        orArg.add(new Atomic(FOL.mkEq(ft, e.getValue().get(i))));
                                    else
                                        orArg.add(new Atomic(FOL.mkEq(e.getValue().get(i), ft)));
                                }
                                generalGroundedFormulaList.add(mkAssert(new Or(orArg).toSMTLIB()));
                                include = Math.min(include + 1, len);
                                j++;
                            }
                        }
                        do {
                            if (flag && p.left.size() == 1) {
                                //System.out.println("YES");
                                break;
                            }
                            for (i = 0; i != bounds.length; i++)
                                args.set(i, universe.get(typeList[i]).get(counter.digits[i]));
                            counter.inc();
                            boolean pass = false;
                            if (flag){
                                Set<Term> set = new HashSet<>();
                                for (Term a: args)
                                    if (a.getType().equals(p.right))
                                        set.add(a);
                                pass = set.size() == 1;
                            }
                            if (pass) {
                                //System.out.println("Pass");
                                continue;
                            }
                            Term ft = FOL.apply(c, args);
                            if (theory.constantSet.contains(c))
                                getModelDeclarationList.add(ft.toSMTLIB());
                            if (include != 1){
                                SortedSet<Formula> orArg = new TreeSet<>();
                                for (i = 0; i != include; i++) {
                                    if (ft.compareTo(e.getValue().get(i)) > 0)
                                        orArg.add(new Atomic(FOL.mkEq(ft, e.getValue().get(i))));
                                    else
                                        orArg.add(new Atomic(FOL.mkEq(e.getValue().get(i), ft)));
                                }
                                generalGroundedFormulaList.add(mkAssert(new Or(orArg).toSMTLIB()));
                            } else {
                                if (ft.compareTo(e.getValue().get(0)) > 0)
                                    simpleGroundedFormulaList.add(mkAssert(new Atomic(FOL.mkEq(ft, e.getValue().get(0))).toSMTLIB()));
                                else
                                    simpleGroundedFormulaList.add(mkAssert(new Atomic(FOL.mkEq(e.getValue().get(0), ft)).toSMTLIB()));
                            }
                            include = Math.min(include + 1, len);
                        } while (counter.hasNext());
                    }

                }
            }
            return;
        }
        else {
            List<Con> constants = new LinkedList<>();
            constants.addAll(theory.constantSet);
            constants.addAll(helperConstants);
            for (Con c: constants){
                //System.out.println(c);
                Pair<List<PTerm>, PTerm> p = Type.brkFnTys(c.getType());
                if (p.left.isEmpty()){
                    if (theory.constantSet.contains(c))
                        getModelDeclarationList.add(new StrExpr(c.getName()));
                    SortedSet<Formula> orArg = new TreeSet<>();
                    for (Con cv: universe.get(p.right))
                        if (c.compareTo(cv) > 0)
                            orArg.add(new Atomic(FOL.mkEq(c, cv)));
                        else
                            orArg.add(new Atomic(FOL.mkEq(cv, c)));
                    generalGroundedFormulaList.add(mkAssert(new Or(orArg).toSMTLIB()));
                } else {
                    int [] bounds = new int[p.left.size()];
                    PTerm [] typeList = new PTerm[bounds.length];
                    int i = 0;
                    for (PTerm pty: p.left){
                        bounds[i] = universe.get(pty).size();
                        typeList[i++] = pty;
                    }
                    Counter counter = new Counter(bounds);
                    ArrayList<Term> args = new ArrayList<>(bounds.length);
                    for (i = 0; i!= bounds.length; i++)
                        args.add(null);
                    do {
                        for (i = 0; i != bounds.length; i++)
                            args.set(i, universe.get(typeList[i]).get(counter.digits[i]));
                        counter.inc();
                        Term ft = FOL.apply(c, args);
                        if (theory.constantSet.contains(c)) {
                            //System.out.println(ft);
                            getModelDeclarationList.add(ft.toSMTLIB());
                        }
                        SortedSet<Formula> orArg = new TreeSet<>();
                        for (Con cv: universe.get(p.right))
                            if (ft.compareTo(c) > 0)
                                orArg.add(new Atomic(FOL.mkEq(ft, cv)));
                            else
                                orArg.add(new Atomic(FOL.mkEq(cv, ft)));
                        generalGroundedFormulaList.add(mkAssert(new Or(orArg).toSMTLIB()));
                    } while (counter.hasNext());
                }
            }
        }
    }

    private void expandQuantifiers(){
        int c = 0;
        int len = FOLFormulas.size();
        //FOLFormulas.sort((f1, f2) -> f2.compareTo(f1));
        for (Formula f: FOLFormulas){
            /*
            c++;
            if (verbosity > 0)
                System.out.println(c + "/" + len + " : " + f);
            */
            if (f.isFalse()) {
                //System.out.println("HERE");
                isSat = -1;
                return;
            }
            if (f.isTrue())
                continue;
            //System.out.println(f);
            if (!f.isForall()){
                if (f.isLiteral()){
                    simpleGroundedFormulaList.add(mkAssert(f.toSMTLIB()));
                    if (f.isNot())
                        learnedLiterals.put(((Atomic)((Not)f).getBody()).getBody(), Formula.false_);
                    else
                        learnedLiterals.put(((Atomic) f).getBody(), Formula.true_);
                }
                else
                    generalGroundedFormulaList.add(mkAssert(f.toSMTLIB()));
                continue;
                /*
                generalGroundedFormulaList.add(mkAssert(f.toSMTLIB()));
                continue;
                */
            }
            Forall fa = (Forall) f;
            SortedSet<Var> vars = fa.getVars();
            int bounds[] = new int[vars.size()];
            PTerm [] typeList = new PTerm[bounds.length];
            Map<Var, Term> sub = new HashMap<>(vars.size());
            int i = 0;
            for (Var v: vars) {
                typeList[i] = v.getType();
                bounds[i] = universe.get(typeList[i]).size();
                i++;
            }
            Counter counter = new Counter(bounds);
            Formula body = fa.getBody();
            do{
                i = 0;
                for (Var v: vars){
                    sub.put(v, universe.get(typeList[i]).get(counter.digits[i]));
                    i++;
                }
                counter.inc();
                Formula gs = body.substitute(sub).simplifyEQ(learnedLiterals, pairwiseDistinct);
                if (gs.equals(Formula.false_)) {
                    //System.out.println(fa);
                    //System.out.println(sub);
                    isSat = -1;
                    return;
                }
                if (gs.equals(Formula.true_))
                    continue;
                if (gs.isLiteral()){
                    //System.out.println("learned: " + gs + " from " + fa);

                    if (gs.isNot())
                        learnedLiterals.put(((Atomic)((Not)gs).getBody()).getBody(), Formula.false_);
                    else
                        learnedLiterals.put(((Atomic) gs).getBody(), Formula.true_);

                    simpleGroundedFormulaList.add(mkAssert(gs.toSMTLIB()));
                }
                else generalGroundedFormulaList.add(mkAssert(gs.toSMTLIB()));
            } while (counter.hasNext());

        }
    }

    private void ground(boolean symmetry){
        //translateSorts();
        translateConstants();
        translateDefinitions();
        if (verbosity > 0 && !is_quantifier_free)
            System.out.println("Generating range constraints:");
        if (!is_quantifier_free)
            generateRangeConstraints(symmetry);
        if (verbosity > 0 && !is_quantifier_free)
            System.out.println("Grounding:");
        expandQuantifiers();
    }

    private void runSolver(boolean generateModel){
        try {
            File tempScript = File.createTempFile("tmp-smtlib-fortress", ".smt");
            System.out.println("Creating the SMT-LIB2 file:");
            tempScript.deleteOnExit();
            BufferedWriter bw = new BufferedWriter(new FileWriter(tempScript));
            for (SExpr s: declarationList) {
                bw.write(s.toString());
                bw.newLine();
            }
            for (SExpr s: simpleGroundedFormulaList) {
                bw.write(s.toString());
                bw.newLine();
            }
            for (SExpr s: generalGroundedFormulaList) {
                bw.write(s.toString());
                bw.newLine();
            }
            bw.write("(check-sat)");
            if (generateModel){
                System.out.println("Adding get-value:");
                bw.newLine();
                bw.write(new ComExpr(new StrExpr("get-value"), new ComExpr(getModelDeclarationList)).toString());
            }
            bw.close();

            //String command = "cvc4 ";
            //String commandArgs = "--lang=smt2 ";
            //String command = "mathsat5 ";
            //String commandArgs = "-input=smt2 ";
            String command = "z3 ";
            String commandArgs = "-smt2 ";
            String call = command + commandArgs ;
            System.out.println("Running SMT solver with the following command:");
            System.out.println(call);
            Process p = Runtime.getRuntime().exec(call + tempScript.getAbsolutePath());
            BufferedReader br = new BufferedReader(new InputStreamReader(p.getInputStream()));
            System.out.println("Running SMT solver...");
            //System.out.println(br);
            String firstLine = br.readLine();
            System.out.println("*********************");
            //System.out.println(firstLine);
            if (firstLine.equals("sat"))
                isSat = 1;
            else isSat = -1;
            if (isSat < 0)
                System.out.println("Theory is not consistent with respect to the provided bounds.");
            else {
                System.out.println("Theory is consistent.");
                if (generateModel) {
                    System.out.println("Here is a satisfying model:");
                    Map<String, Con> constantValue = new HashMap<>(universeSize * 2);
                    model = new TreeMap<>();
                    Map<String, Con> domainConst = new TreeMap<>();
                    for (Map.Entry<PTerm, List<Con>> e : universe.entrySet()) {
                        System.out.println(e.getKey() + " = " + e.getValue());
                        for (Con c: e.getValue())
                            domainConst.put(c.getName(), c);
                    }
                    //System.out.println(domainConst);
                    for (int i = 0; i != universeSize; i++) {
                        String line = br.readLine();
                        StringTokenizer stline = new StringTokenizer(line, " ()");
                        Con c = domainConst.get(stline.nextToken());
                        constantValue.put(stline.nextToken(), c);
                    }
                    //System.out.println(constantValue);
                    //System.out.println(universeSize);
                    //System.out.println(getModelDeclarationList.size());
                    for (int i = universeSize; i != getModelDeclarationList.size(); i++) {
                        String line = br.readLine();
                        StringTokenizer st = new StringTokenizer(line, " ()");
                        Con fun = (Con) theory.getTermByName(st.nextToken()).get();
                        List<Term> funArg = new LinkedList<>();
                        String last;
                        do {
                            last = st.nextToken();
                            Term ot = domainConst.getOrDefault(last, null);
                            if (ot != null)
                                funArg.add(ot);
                        } while (st.hasMoreTokens());
                        Con value = constantValue.get(last);
                        if (funArg.isEmpty()) {
                            System.out.println(fun + " = " + value);
                            model.put(fun, value);
                        } else {
                            Term tempp = FOL.apply(fun, funArg);
                            System.out.println(tempp + " = " + value);
                            model.put(tempp, value);
                        }
                    }
                }
            }
            p.waitFor();
            p.destroy();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

    }

    private void generateSMTLIB(String caseStudy, int size, boolean generateModel){
        try {
            File script = new File(caseStudy + "-" + Integer.toString(size) + ".smt");
            System.out.println("Creating the SMT-LIB2 file:");
            BufferedWriter bw = new BufferedWriter(new FileWriter(script));
            for (SExpr s: declarationList) {
                bw.write(s.toString());
                bw.newLine();
            }
            for (SExpr s: simpleGroundedFormulaList) {
                bw.write(s.toString());
                bw.newLine();
            }
            for (SExpr s: generalGroundedFormulaList) {
                bw.write(s.toString());
                bw.newLine();
            }
            bw.write("(check-sat)");
            if (generateModel){
                System.out.println("Adding get-value:");
                bw.newLine();
                bw.write(new ComExpr(new StrExpr("get-value"), new ComExpr(getModelDeclarationList)).toString());
            }
            bw.close();

            //String command = "cvc4 ";
            //String commandArgs = "--lang=smt2 ";
            //String command = "mathsat5 ";
            //String commandArgs = "-input=smt2 ";
            //String command = "z3 ";
            //String commandArgs = "-smt2 ";
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    public boolean checkSat(boolean symmetry, boolean generateModel){
        Timer timer = new Timer();
        if (verbosity <= 0)
            timer = null;
        ground(symmetry);
        if (verbosity > 0)
            timer.stop();
        if (isSat < 0) {
            System.out.println("Trivially unsat.");
            return false;
        }
        if (verbosity > 0)
            timer.set();
        runSolver(generateModel);
        if (verbosity > 0)
            timer.stop();
        return isSat > 0;
    }

    // Generates an SMT-LIB file
    public void generate(boolean symmetry, boolean generateModel, String name, int size){
        Timer timer = new Timer();
        if (verbosity <= 0)
            timer = null;
        ground(symmetry);
        if (verbosity > 0)
            timer.stop();
        if (isSat < 0) {
            System.out.println("Trivially unsat.");
            return;
        }
        if (verbosity > 0)
            timer.set();
        generateSMTLIB(name, size, generateModel);
        if (verbosity > 0)
            timer.stop();
    }

}