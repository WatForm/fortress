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
import fortress.lambda.Con;
import fortress.lambda.Term;
import fortress.lambda.Var;
import fortress.formats.smt.smtlib.SExpr;
import fortress.formats.smt.smtlib.StrExpr;
import fortress.util.Pair;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static fortress.util.Errors.failIf;

public class False extends Formula {
    
    static final False INSTANCE = new False();
    
    False(){}

    @Override
    public boolean isFalse() {
        return true;
    }

    @Override
    public boolean isTrue() {
        return false;
    }

    @Override
    public boolean isAtomic() {
        return false;
    }

    @Override
    public boolean isNot() {
        return false;
    }

    @Override
    public boolean isAnd() {
        return false;
    }

    @Override
    public boolean isOr() {
        return false;
    }

    @Override
    public boolean isImp() {
        return false;
    }

    @Override
    public boolean isIff() {
        return false;
    }

    @Override
    public boolean is_quantifier_free() {
        return true;
    }

    @Override
    public boolean isForall() {
        return false;
    }

    @Override
    public boolean isExists() {
        return false;
    }

    @Override
    public String toString() {
        return Constants.FALSE_Str;
    }

    @Override
    public boolean equals(Object o) {
        if (o == this)
            return true;
        if (o == null)
            return false;
        return getClass() == o.getClass();
    }

    @Override
    public int compareTo(Formula o) {
        if (o == this)
            return 0;
        failIf(o == null);
        if (getClass() != o.getClass())
            return -1;
        return 0;
    }

    @Override
    public int hashCode() {
        final int prime = 23;
        return prime;
    }

    @Override
    void fvH(Set<Var> acc) {

    }

    @Override
    public Formula substitute(Var v, Term t) {
        return this;
    }

    @Override
    public Formula substitute(Map<Var, Term> sub) {
        return this;
    }


    @Override
    public <T> T accept(FormulaVisitor<T> v) {
        return v.visitFalse(this);
    }


    @Override
    public SExpr toSMTLIB(){
        return new StrExpr(Constants.smtlibOf.getOrDefault(Constants.FALSE_Str, Constants.FALSE_Str));
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
        return this;
    }

}
