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

package fortress.fol.visitor;

import fortress.fol.*;
import fortress.lambda.Term;
import fortress.lambda.Var;
import fortress.util.Pair;

import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

/**
 * Created by Amirhossein Vakili.
 */
public class FormulaFlattenTerm implements FormulaVisitor<Formula>{

    private int acc;

    public FormulaFlattenTerm(int acc){
        this.acc = acc;
    }

    @Override
    public Formula visitFalse(False f) {
        return f;
    }

    @Override
    public Formula visitTrue(True f) {
        return f;
    }

    @Override
    public Formula visitAtomic(Atomic f) {
        Pair<List<Pair<Var, Term>>, Term> temp = f.getBody().flatTerm(acc);
        if (temp.left.isEmpty())
            return f;
        acc += temp.left.size();
        SortedSet<Var> vars = new TreeSet<>();
        SortedSet<Formula> andBody = new TreeSet<>();
        for(Pair<Var, Term> p: temp.left){
            vars.add(p.left);
            andBody.add(new Atomic(Term.mkEq(p.left, p.right)));
        }
        return new Forall(vars, new Imp(new And(andBody), new Atomic(temp.right)));
    }

    @Override
    public Formula visitNot(Not f) {
        return new Not(f.getBody().accept(this));
    }

    @Override
    public Formula visitAnd(And f) {
        SortedSet<Formula> temp = new TreeSet<>();
        for (Formula ff: f.getBody())
            temp.add(ff.accept(this));
        return new And(temp);
    }

    @Override
    public Formula visitOr(Or f) {
        SortedSet<Formula> temp = new TreeSet<>();
        for (Formula ff: f.getBody())
            temp.add(ff.accept(this));
        return new Or(temp);
    }

    @Override
    public Formula visitImp(Imp f) {
        return new Imp(f.getLeft().accept(this), f.getRight().accept(this));
    }

    @Override
    public Formula visitIff(Iff f) {
        return new Iff(f.getLeft().accept(this), f.getRight().accept(this));
    }

    @Override
    public Formula visitForall(Forall f) {
        return new Forall(f.getVars(), f.getBody().accept(this));
    }

    @Override
    public Formula visitExists(Exists f) {
        return new Exists(f.getVars(), f.getBody().accept(this));
    }
}