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
public class Not extends Formula {

    private Formula body;

    public Not(Formula body){
        failIf(body == null);
        this.body = body;
    }

    public Formula getBody(){
        return body;
    }

    @Override
    public boolean isNot() {
        return true;
    }

    @Override
    public boolean isLiteral() {
        return body.isAtomic();
    }

    @Override
    public boolean is_quantifier_free() {
        return body.is_quantifier_free();
    }

    @Override
    public String toString() {
        return Constants.NOT_Str  + "[" + body.toString() + "]";
    }

    @Override
    public boolean equals(Object o) {
        if (o == this)
            return true;
        if (o == null)
            return false;
        if (getClass() != o.getClass())
            return false;
        Not temp = ((Not) o);
        return body.equals(temp.body);
    }

    @Override
    public int compareTo(Formula o) {
        failIf(o == null);
        if (o == this)
            return 0;
        Class oc = o.getClass();
        if (oc == False.class || oc == True.class || oc == Atomic.class)
            return 1;
        if (getClass() != o.getClass())
            return -1;
        Not temp = ((Not) o);
        return body.compareTo(temp.body);
    }

    @Override
    public int hashCode() {
        final int prime = 37;
        int result = 1;
        result = prime * result + body.hashCode();
        return result;
    }

    @Override
    public <T> T accept(FormulaVisitor<T> v){
        return v.visitNot(this);
    }

    @Override
    public SExpr toSMTLIB(){
        String n = Constants.smtlibOf.getOrDefault(Constants.NOT_Str, Constants.NOT_Str);
        return new ComExpr(new StrExpr(n), body.toSMTLIB());
    }

    @Override
    void fvH(Set<Var> acc) {
        body.fvH(acc);
    }

    @Override
    public Formula substitute(Var v, Term t) {
        return new Not(body.substitute(v, t));
    }

    @Override
    public Formula substitute(Map<Var, Term> sub) {
        return new Not(body.substitute(sub));
    }

    @Override
    public Formula nnf(){
        if (body.isNot())
            return ((Not) body).body.nnf();
        if (body.isAnd()){
            SortedSet<Formula> temp = new TreeSet<>();
            for (Formula f: ((And) body).getBody())
                temp.add(new Not(f).nnf());
            return new Or(temp);
        }
        if (body.isOr()){
            SortedSet<Formula> temp = new TreeSet<>();
            for (Formula f: ((Or) body).getBody())
                temp.add(new Not(f).nnf());
            return new And(temp);
        }
        if (body.isImp()){
            SortedSet<Formula> temp = new TreeSet<>();
            Imp f = (Imp) body;
            temp.add(f.getLeft().nnf());
            temp.add(new Not(f.getRight()).nnf());
            return new And(temp);
        }
        if (body.isIff()){
            SortedSet<Formula> temp1 = new TreeSet<>();
            SortedSet<Formula> temp2 = new TreeSet<>();
            SortedSet<Formula> temp3 = new TreeSet<>();
            Iff f = (Iff) body;
            temp2.add(f.getLeft().nnf());
            temp2.add(new Not(f.getRight()).nnf());
            temp1.add(new And(temp2));
            temp3.add(new Not(f.getLeft()).nnf());
            temp3.add(f.getRight().nnf());
            temp1.add(new And(temp3));
            return new Or(temp1);
        }
        if (body.isForall()){
            Forall temp = (Forall) body;
            return new Exists(temp.getVars(), new Not(temp.getBody()).nnf());
        }
        if (body.isExists()){
            Exists temp = (Exists) body;
            return new Forall(temp.getVars(), new Not(temp.getBody()).nnf());
        }
        return this;
    }

    @Override
    Formula simplify1(){
        if (body.equals(true_))
            return false_;
        if (body.equals(false_))
            return true_;
        if (body.isNot())
            return ((Not) body).getBody();
        return this;
    }

    @Override
    public Formula simplify(){
        return new Not(body.simplify()).simplify1();
    }

    @Override
    Pair<Formula, Integer> skolemizeH(int acc, List<Term> argumentList, List<PTerm> typeList, List<Const> skolemFunList) {
        return new Pair<>(this, acc);
    }

    @Override
    public Formula prenex() {
        return this;
    }

    @Override
    public Formula simplifyEQ(Map<Term, Formula> literlas, List<Set<Term>> pairwiseDistinct){
        Formula temp = body.simplifyEQ(literlas, pairwiseDistinct);
        if (temp.equals(Formula.true_))
            return Formula.false_;
        if (temp.equals(Formula.false_))
            return Formula.true_;
        return this;
    }

}