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

package fortress.lambda;

import static fortress.lambda.Type.*;
import static fortress.util.Errors.failIf;

import fortress.Constants;
import fortress.fol.pterm.PTerm;

import fortress.lambda.visitor.MaxIDTerm;
import fortress.lambda.visitor.TermVisitor;
import fortress.formats.smt.smtlib.ComExpr;
import fortress.formats.smt.smtlib.SExpr;
import fortress.formats.smt.smtlib.StrExpr;

import fortress.util.Pair;


import java.util.*;
import java.util.stream.Collectors;



/**
 * Created by Amirhossein Vakili.
 */

 /*
 Typed lambda calculus terms
 term ::=
    | Var (variable)
    | Const (constant)
    | App (application)
    | Abs (abstraction)
 */
public abstract class Term implements Comparable<Term>{

    PTerm ty;

    public static Const EQ = new Const(Constants.EQ_Str, mkFnTy(_a, _a, BOOL));

    public static App mkEq(Term t1, Term t2){
        return new App(new App(EQ, t1), t2);
    }

    public PTerm getType(){
        return ty;
    }

    public abstract boolean isVar();

    public abstract boolean isCon();

    public abstract boolean isApp();

    public abstract boolean isAbs();

    @Override
    public abstract String toString();

    @Override
    public abstract boolean equals(Object obj);

    @Override
    public abstract int hashCode();

    public abstract <T> T accept(TermVisitor<T> v);

    public void print(){
        System.out.println(this + " : " + ty);
    }

    protected abstract void constantsH(Set<Const> acc);

    public Set<Const> constantSet(){
        Set<Const> result = new HashSet<>();
        this.constantsH(result);
        return result;
    }

    protected abstract void typeFunctorsH(Set<Pair<String, Integer>> acc);

    public Set<Pair<String, Integer>> typeFunctorSet(){
        Set<Pair<String, Integer>> result = new HashSet<>();
        this.typeFunctorsH(result);
        return result;
    }

    protected abstract void fvH(Set<Var> acc);

    // Free variables
    public Set<Var> fv(){
        Set<Var> result = new HashSet<>();
        this.fvH(result);
        return result;
    }

    public abstract Term substitute(Var v, Term t);

    public abstract Term substitute(Map<Var, Term> sub);

    abstract Pair<Term, Integer> distinctVarH(String id, int acc);

    public Term distinctVar(String id){
        return distinctVarH(id, accept(new MaxIDTerm(id))).left;
    }

    public boolean isClosed(){
        return fv().isEmpty();
    }

    public List<Term> brkApp(){
        List<Term> result = new ArrayList<>();
        Term temp = this;
        while (temp.isApp()){
            result.add(0, ((App) temp).getArg());
            temp = ((App) temp).getFun();
        }
        result.add(0, temp);
        return result;
    }

    public Pair<List<Var>, Term> brkAbs(){
        List<Var> varList = new ArrayList<>();
        Term temp = this;
        while (temp.isAbs()){
            varList.add(((Abs) temp).getArg());
            temp = ((Abs) temp).getFun();
        }
        return new Pair<>(varList, temp);
    }

    public SExpr toSMTLIB(){
        if (!isApp()) {
            String temp = toString();
            return new StrExpr(Constants.smtlibOf.getOrDefault(temp, temp));
        }
        return new ComExpr(brkApp().stream().map(Term::toSMTLIB).collect(Collectors.toList()));
    }

    public boolean isUnary(Const c){
        if (!isApp())
            return false;
        final App temp = (App) this;
        return temp.getFun().equals(c);
    }

    public static App mkUnary(Const c, Term t){
        return new App(c, t);
    }

    public Term brkUnary(Const c){
        failIf(!isUnary(c));
        return ((App) this).getArg();
    }

    public boolean isBinary(Const c){
        if (!isApp())
            return false;
        final App temp = (App) this;
        if (!temp.isApp())
            return false;
        return temp.getFun().equals(c);
    }

    public static App mkBinary(Const c, Term t1, Term t2){
        return new App(new App(c, t1), t2);
    }

    public Pair<Term, Term> brkBinary(Const c){
        failIf(!isBinary(c));
        App temp = (App) this;
        return new Pair<>(((App) temp.getFun()).getArg(), temp.getArg());
    }

    public boolean isEq(){
        if (!this.isApp())
            return false;
        Term temp = ((App) this).getFun();
        if (!temp.isApp())
            return false;
        return ((App)temp).getFun().equals(EQ);
    }

    public Pair<Term, Term> brkEq(){
        failIf(!isEq());
        App temp = (App) this;
        return new Pair<>(((App) temp.getFun()).getArg(), temp.getArg());
    }

    public Pair<List<Pair<Var, Term>>, Term> flatTerm(int acc){
        List<Term> lt = brkApp();
        List<Pair<Var, Term>> varTerms = new LinkedList<>();
        int currentIndex = acc;
        for (int i = 1; i < lt.size(); i++){
            Pair<List<Pair<Var, Term>>, Term> temp = lt.get(i).flatTerm(currentIndex);
            currentIndex += temp.left.size();
            varTerms.addAll(temp.left);
            if (temp.right.isApp() && !lt.get(0).equals(EQ)){
                Var newT = new Var("ft" + Integer.toString(currentIndex), temp.right.ty);
                varTerms.add(new Pair<>(newT, temp.right));
                currentIndex++;
                lt.set(i, newT);
            }
            else
                lt.set(i, temp.right);
        }
        return new Pair<>(varTerms, App.mkApp(lt));
    }

}
