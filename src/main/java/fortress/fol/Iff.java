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
public class Iff extends Formula {

    private Formula left;
    private Formula right;

    public Iff(Formula left, Formula right){
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
    public boolean isIff() {
        return true;
    }

    @Override
    public boolean is_quantifier_free() {
        return left.is_quantifier_free() && right.is_quantifier_free();
    }

    @Override
    public String toString() {
        return  "(" + left.toString() + " " + Constants.IFF_Str + " " + right.toString() + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (o == this)
            return true;
        if (o == null)
            return false;
        if (getClass() != o.getClass())
            return false;
        Iff temp = ((Iff) o);
        return left.equals(temp.left) && right.equals(temp.right);
    }

    @Override
    public int compareTo(Formula o) {
        failIf(o == null);
        if (o == this)
            return 0;
        Class oc = o.getClass();
        if (oc == Exists.class || oc == Forall.class)
            return -1;
        if (getClass() != o.getClass())
            return 1;
        Iff temp = ((Iff) o);
        int test = left.compareTo(temp.left);
        if (test != 0)
            return test;
        return right.compareTo(temp.right);
    }

    @Override
    public int hashCode() {
        final int prime = 37;
        int result = 1;
        result = prime * result + left.hashCode();
        result = prime * result + right.hashCode();
        return result;
    }

    @Override
    public <T> T accept(FormulaVisitor<T> v){
        return v.visitIff(this);
    }

    @Override
    public SExpr toSMTLIB(){
        List<SExpr> temp = new ArrayList<>();
        temp.add(new StrExpr(Constants.smtlibOf.getOrDefault(Constants.IFF_Str, Constants.IFF_Str)));
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
        return new Iff(left.substitute(v, t), right.substitute(v, t));
    }

    @Override
    public Formula substitute(Map<Var, Term> sub) {
        return new Iff(left.substitute(sub), right.substitute(sub));
    }

    @Override
    public Formula nnf(){
        SortedSet<Formula> temp1 = new TreeSet<>();
        SortedSet<Formula> temp2 = new TreeSet<>();
        SortedSet<Formula> temp3 = new TreeSet<>();

        temp2.add(left.nnf());
        temp2.add(right.nnf());

        temp3.add(new Not(left).nnf());
        temp3.add(new Not(right).nnf());

        temp1.add(new And(temp2));
        temp1.add(new And(temp3));

        return new Or(temp1);
    }

    @Override
    Formula simplify1(){
        if (left.equals(true_))
            return right;
        if (left.equals(false_)) {
            if (right.equals(false_))
                return true_;
            return new Not(right);
        }
        if (right.equals(true_))
            return left;
        if (right.equals(false_))
            return new Not(left);
        if (right.equals(left))
            return true_;
        if (left.equals(new Not(right)) || right.equals(new Not(left)))
            return false_;
        return this;
    }

    @Override
    public Formula simplify(){
        return new Iff(left.simplify(), right.simplify()).simplify1();
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
