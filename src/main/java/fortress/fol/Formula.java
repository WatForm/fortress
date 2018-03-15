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

package fortress.fol;

import fortress.fol.pterm.PTerm;
import fortress.fol.visitor.FormulaVisitor;
import fortress.lambda.Const;
import fortress.lambda.Term;
import fortress.lambda.Var;
import fortress.formats.smt.smtlib.SExpr;
import fortress.util.Pair;

import java.util.*;

import static fortress.util.Errors.failIf;

public abstract class Formula implements Comparable<Formula>{

    public static False false_ = False.INSTANCE;

    public static True true_ = True.INSTANCE;

    public boolean isFalse(){
        return false;
    }

    public boolean isTrue(){
        return false;
    }

    public boolean isAtomic(){
        return false;
    }

    public boolean isNot(){
        return false;
    }

    public boolean isLiteral(){
        return false;
    }

    public boolean isAnd(){
        return false;
    }

    public boolean isOr(){
        return false;
    }

    public boolean isImp(){
        return false;
    }

    public boolean isIff(){
        return false;
    }

    public abstract boolean is_quantifier_free();

    public boolean isForall(){
        return false;
    }

    public boolean isExists(){
        return false;
    }

    @Override
    public abstract String toString();

    @Override
    public abstract boolean equals(Object o);

    @Override
    public abstract int hashCode();

    public abstract <T> T accept(FormulaVisitor<T> v);

    public abstract SExpr toSMTLIB();

    public static Formula fromTerm(Term t){
        failIf(!t.getType().equals(FOL.bool));

        if (FOL.isFalse(t))
            return false_;

        if (FOL.isTrue(t))
            return true_;

        if (FOL.isNot(t)) {
            return new Not(fromTerm(FOL.brkNot(t)));
        }

        if (FOL.isAnd(t)){
            SortedSet<Formula> body = new TreeSet<>();
            List<Term> translated = new ArrayList<>();
            for(Term tt: FOL.brkAnds(t)) {
                if (translated.contains(tt))
                    continue;
                translated.add(tt);
                body.add(fromTerm(tt));
            }
            return new And(body);
        }

        if (FOL.isOr(t)){
            SortedSet<Formula> body = new TreeSet<>();
            List<Term> translated = new ArrayList<>();
            for(Term tt: FOL.brkOrs(t)) {
                if (translated.contains(tt))
                    continue;
                translated.add(tt);
                body.add(fromTerm(tt));
            }
            return new Or(body);
        }

        if (FOL.isImp(t)) {
            Pair<Term, Term> p = FOL.brkImp(t);
            return new Imp(fromTerm(p.left), fromTerm(p.right));
        }

        if (FOL.isIff(t)) {
            Pair<Term, Term> p = FOL.brkIff(t);
            return new Iff(fromTerm(p.left), fromTerm(p.right));
        }

        if (FOL.isForall(t)){
            Pair<List<Var>, Term> p = FOL.brkForalls(t);
            SortedSet<Var> vars = new TreeSet<>();
            Set<Var> freeVar = p.right.fv();
            for (Var v: p.left)
                if (freeVar.contains(v))
                    vars.add(v);
            return new Forall(vars, fromTerm(p.right));
        }

        if (FOL.isExists(t)){
            Pair<List<Var>, Term> p = FOL.brkExistss(t);
            SortedSet<Var> vars = new TreeSet<>();
            Set<Var> freeVar = p.right.fv();
            for (Var v: p.left)
                if (freeVar.contains(v))
                    vars.add(v);
            return new Exists(vars, fromTerm(p.right));
        }
        return new Atomic(t);
    }


    abstract void fvH(Set<Var> acc);

    public Set<Var> fv(){
        Set<Var> result = new TreeSet<>();
        fvH(result);
        return result;
    }

    public abstract Formula substitute(Var v, Term t);

    public abstract Formula substitute(Map<Var, Term> sub);

    public abstract Formula nnf();

    abstract Formula simplify1();

    public abstract Formula simplify();

    abstract Pair<Formula, Integer> skolemizeH(int acc, List<Term> argumentList, List<PTerm> typeList, List<Const> skolemFunList);

    public Pair<Formula, List<Const>> skolemize(int acc){
        List<Term> argumentList = new ArrayList<>();
        List<PTerm> typeList = new ArrayList<>();
        List<Const> skolemFunList = new ArrayList<>();
        Formula f = skolemizeH(acc, argumentList, typeList, skolemFunList).left;
        return new Pair<>(f, skolemFunList);
    }

    public abstract Formula prenex();

    public Formula bodyOfprenex(){
        Formula result = this;
        while (result.isForall() || result.isExists())
            result = result.isForall() ? ((Forall) result).getBody() : ((Exists) result).getBody();
        return result;
    }

    public Formula simplifyEQ(Map<Term, Formula> literlas, List<Set<Term>> pairwiseDistinct){
        System.out.println("Formula must be in normal negation form and quantifier free");
        failIf(true);
        return null;
    }

}