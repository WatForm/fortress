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

import java.util.Set;
import java.util.TreeSet;

/**
 * Created by Amirhossein Vakili.
 */
public class FormulaFV implements FormulaVisitor<Set<Var>> {

    private Set<Var> acc;

    public FormulaFV(){
        acc = new TreeSet<>();
    }

    @Override
    public Set<Var> visitFalse(False f) {
        return acc;
    }

    @Override
    public Set<Var> visitTrue(True f) {
        return acc;
    }

    @Override
    public Set<Var> visitAtomic(Atomic f) {
        acc.addAll(f.getBody().fv());
        return acc;
    }

    @Override
    public Set<Var> visitNot(Not f) {
        f.getBody().accept(this);
        return acc;
    }

    @Override
    public Set<Var> visitAnd(And f) {
        for(Formula ff: f.getBody())
            ff.accept(this);
        return acc;
    }

    @Override
    public Set<Var> visitOr(Or f) {
        for(Formula ff: f.getBody())
            ff.accept(this);
        return acc;
    }

    @Override
    public Set<Var> visitImp(Imp f) {
        f.getLeft().accept(this);
        f.getRight().accept(this);
        return acc;
    }

    @Override
    public Set<Var> visitIff(Iff f) {
        f.getLeft().accept(this);
        f.getRight().accept(this);
        return acc;
    }

    @Override
    public Set<Var> visitForall(Forall f) {
        f.getBody().accept(this);
        for(Var v: f.getVars())
            acc.remove(v);
        return acc;
    }

    @Override
    public Set<Var> visitExists(Exists f) {
        f.getBody().accept(this);
        for(Var v: f.getVars())
            acc.remove(v);
        return acc;
    }
}