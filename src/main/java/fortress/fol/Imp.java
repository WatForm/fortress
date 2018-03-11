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

import fortress.Constants;
import fortress.fol.pterm.PTerm;
import fortress.fol.visitor.FormulaVisitor;
import fortress.lambda.Const;
import fortress.lambda.Term;
import fortress.lambda.Var;
import fortress.formats.smt.smtlib.ComExpr;
import fortress.formats.smt.smtlib.SExpr;
import fortress.formats.smt.smtlib.StrExpr;
import fortress.util.Pair;

import java.util.*;

import static fortress.util.Errors.failIf;

/**
 * Created by amirhossein on 15/01/16.
 */
public class Imp extends Formula {

    private Formula left;
    private Formula right;

    public Imp(Formula left, Formula right){
        failIf(left == null);
        failIf(right == null);
        this.left = left;
        this.right = right;
    }

    public Formula getLeft(){
        return left;
    }

    public Formula getRight(){
        return right;
    }

    @Override
    public boolean isImp() {
        return true;
    }

    @Override
    public boolean is_quantifier_free() {
        return left.is_quantifier_free() && right.is_quantifier_free();
    }

    @Override
    public String toString() {
        return  "(" + left.toString() + " " + Constants.IMP_Str + " " + right.toString() + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (o == this)
            return true;
        if (o == null)
            return false;
        if (getClass() != o.getClass())
            return false;
        Imp temp = ((Imp) o);
        return left.equals(temp.left) && right.equals(temp.right);
    }

    @Override
    public int compareTo(Formula o) {
        failIf(o == null);
        if (o == this)
            return 0;
        Class oc = o.getClass();
        if (oc == Exists.class || oc == Forall.class || oc == Iff.class)
            return -1;
        if (getClass() != o.getClass())
            return 1;
        Imp temp = ((Imp) o);
        int test = left.compareTo(temp.left);
        if (test != 0)
            return test;
        return right.compareTo(temp.right);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + left.hashCode();
        result = prime * result + right.hashCode();
        return result;
    }

    @Override
    public <T> T accept(FormulaVisitor<T> v){
        return v.visitImp(this);
    }

    @Override
    public SExpr toSMTLIB(){
        List<SExpr> temp = new ArrayList<>();
        temp.add(new StrExpr(Constants.smtlibOf.getOrDefault(Constants.IMP_Str, Constants.IMP_Str)));
        temp.add(left.toSMTLIB());
        temp.add(right.toSMTLIB());
        return new ComExpr(temp);
    }

    @Override
    void fvH(Set<Var> acc) {
        left.fvH(acc);
        right.fvH(acc);
    }

    @Override
    public Formula substitute(Var v, Term t) {
        return new Imp(left.substitute(v, t), right.substitute(v, t));
    }

    @Override
    public Formula substitute(Map<Var, Term> sub) {
        return new Imp(left.substitute(sub), right.substitute(sub));
    }

    @Override
    public Formula nnf(){
        SortedSet<Formula> temp = new TreeSet<>();
        temp.add(new Not(left).nnf());
        temp.add(right.nnf());
        return new Or(temp);
    }

    @Override
    Formula simplify1(){
        if (left.equals(true_))
            return right;
        if (left.equals(false_))
            return true_;
        if (right.equals(true_))
            return true_;
        if (right.equals(false_))
            return new Not(left);
        if (left.equals(right))
            return true_;
        if (left.equals(new Not(right)) || right.equals(new Not(left)))
            return right;
        return this;
    }

    @Override
    public Formula simplify(){
        return new Imp(left.simplify(), right.simplify()).simplify1();
    }

    @Override
    Pair<Formula, Integer> skolemizeH(int acc, List<Term> argumentList, List<PTerm> typeList, List<Const> skolemFunList) {
        System.out.println("Formula is not in normal negation form.");
        failIf(true);
        return null;
    }

    @Override
    public Formula prenex() {
        System.out.println("Formula is not in normal negation form.");
        failIf(true);
        return null;
    }
}
