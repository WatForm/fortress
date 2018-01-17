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
import fortress.lambda.Con;
import fortress.lambda.Term;
import fortress.lambda.Var;
import fortress.formats.smt.smtlib.SExpr;
import fortress.util.Pair;


import java.util.List;
import java.util.Map;
import java.util.Set;

import static fortress.util.Errors.failIf;

public class Atomic extends Formula {

    private Term body;

    public Atomic(Term body){
        failIf(body == null);
        this.body = body;
    }

    public Term getBody(){
        return body;
    }

    @Override
    public boolean isAtomic() {
        return  true;
    }

    @Override
    public boolean isLiteral(){
        return true;
    }

    @Override
    public boolean is_quantifier_free() {
        return true;
    }

    @Override
    public String toString() {
        return body.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (o == this)
            return true;
        if (o == null)
            return false;
        if (getClass() != o.getClass())
            return false;
        Atomic temp = ((Atomic) o);
        return body.equals(temp.body);
    }

    @Override
    public int compareTo(Formula o) {
        failIf(o == null);
        if (o == this)
            return 0;
        Class oc = o.getClass();
        if (oc == False.class || oc == True.class)
            return 1;
        if (getClass() != o.getClass())
            return -1;
        Atomic temp = ((Atomic) o);
        return body.compareTo(temp.body);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + body.hashCode();
        return result;
    }

    @Override
    public <T> T accept(FormulaVisitor<T> v){
        return v.visitAtomic(this);
    }

    @Override
    public SExpr toSMTLIB(){
        return body.toSMTLIB();
    }


    @Override
    void fvH(Set<Var> acc) {
        acc.addAll(body.fv());
    }

    @Override
    public Formula substitute(Var v, Term t) {
        return new Atomic(body.substitute(v, t));
    }

    @Override
    public Formula substitute(Map<Var, Term> sub) {
        return new Atomic(body.substitute(sub));
    }


    @Override
    public Formula nnf(){
        return this;
    }

    @Override
    Formula simplify1(){
        return this;
    }

    @Override
    public Formula simplify(){
        if (body.isEq()){
            Pair<Term, Term> p = body.brkEq();
            int test = p.left.compareTo(p.right);
            if (test == 0)
                return true_;
            if (test < 0)
                body = Term.mkEq(p.right, p.left);
        }
        return this;
    }

    @Override
    Pair<Formula, Integer> skolemizeH(int acc, List<Term> argumentList, List<PTerm> typeList, List<Con> skolemFunList) {
        return new Pair<>(this, acc);
    }

    @Override
    public Formula prenex() {
        return this;
    }

    @Override
    public Formula simplifyEQ(Map<Term, Formula> literlas, List<Set<Term>> pairwiseDistinct){
        if (FOL.isEq(body)){
            Pair<Term, Term> p = FOL.brkEq(body);
            int test = p.left.compareTo(p.right);
            if (test == 0)
                return true_;
            for (Set<Term> st: pairwiseDistinct)
                if (st.contains(p.left) && st.contains(p.right))
                    return false_;
            if (test < 0)
                body = FOL.mkEq(p.right, p.left);

        }
        return literlas.getOrDefault(body, this);
    }
}
