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

import fortress.Constants;
import fortress.fol.*;
import fortress.fol.pterm.Com;
import fortress.fol.pterm.PTerm;
import fortress.lambda.Con;
import fortress.lambda.Term;
import fortress.lambda.Var;

import java.util.*;

import static fortress.util.Errors.failIf;

/**
 * Created by Amirhossein Vakili.
 */
public class Skolem implements FormulaVisitor<Formula> {

    private int acc;
    private List<Term> argumentList;
    private List<PTerm> typeList;
    public List<Con> skolemFunList;

    public Skolem(int acc){
        this.acc = acc;
        argumentList = new ArrayList<>();
        skolemFunList = new ArrayList<>();
        typeList = new ArrayList<>();
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
        return f;
    }

    @Override
    public Formula visitNot(Not f) {
        return new Not(f.getBody().accept(this));
    }

    @Override
    public Formula visitAnd(And f) {
        SortedSet<Formula> temp = new TreeSet<>();
        for(Formula ff: f.getBody())
            temp.add(ff.accept(this));
        return new And(temp);
    }

    @Override
    public Formula visitOr(Or f) {
        SortedSet<Formula> temp = new TreeSet<>();
        for(Formula ff: f.getBody())
            temp.add(ff.accept(this));
        return new Or(temp);
    }

    @Override
    public Formula visitImp(Imp f) {
        System.out.println("Formula is not in normal negation form.");
        failIf(true);
        return null;
    }

    @Override
    public Formula visitIff(Iff f) {
        System.out.println("Formula is not in normal negation form.");
        failIf(true);
        return null;
    }

    @Override
    public Formula visitForall(Forall f) {
        for(Var v: f.getVars()) {
            argumentList.add(v);
            typeList.add(v.getType());
        }
        return new Forall(f.getVars(), f.getBody().accept(this));
    }

    @Override
    public Formula visitExists(Exists f) {
        Formula temp = f.getBody();
        for(Var v: f.getVars()){
            PTerm type = v.getType();
            for (int i = typeList.size() - 1; i >= 0; i--)
                type = new Com(Constants.FN_Str, new ArrayList<>(Arrays.asList(typeList.get(i), type)));
            Con skolem = new Con("skolem" + Integer.toString(acc++), type);
            skolemFunList.add(skolem);
            Term tt = argumentList.isEmpty()? skolem : FOL.apply(skolem, argumentList);
            temp = temp.substitute(v, tt);
        }
        return temp.accept(this);
    }
}
