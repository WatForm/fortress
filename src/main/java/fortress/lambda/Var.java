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

import fortress.fol.pterm.PTerm;
import fortress.lambda.visitor.TermVisitor;
import fortress.util.Pair;


import java.util.Map;
import java.util.Set;

import static fortress.util.Errors.failIf;

/**
 * Created by amirhossein on 14/01/16.
 */

 // Lambda calculus term for typed variable
public final class Var extends Term {

    private String name;

    public Var(String name, PTerm ty){
        failIf(name == null);
        failIf(ty == null);
        this.name = name;
        this.ty = ty;
    }

    public String getName(){
        return name;
    }

    @Override
    public boolean isVar() {
        return true;
    }

    @Override
    public boolean isCon() {
        return false;
    }

    @Override
    public boolean isApp() {
        return false;
    }

    @Override
    public boolean isAbs() {
        return false;
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Var other = (Var) obj;
        if (!name.equals(other.name))
            return false;
        return ty.equals(other.ty);
    }

    @Override
    public int compareTo(Term o) {
        failIf(o == null);
        if (getClass() != o.getClass())
            return -1;
        Var other = (Var) o;
        if (name.compareTo(other.name) != 0)
            return name.compareTo(other.name);
        return ty.compareTo(other.ty);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + name.hashCode();
        result = prime * result + ty.hashCode();
        return result;
    }

    @Override
    public <T> T accept(TermVisitor<T> v) {
        return v.visitVar(this);
    }

    @Override
    protected void constantsH(Set<Const> acc){
        return;
    }

    @Override
    protected void typeFunctorsH(Set<Pair<String, Integer>> acc){
        for(Pair<String, Integer> p: ty.functors())
            acc.add(p);
    }

    @Override
    protected void fvH(Set<Var> acc){
        acc.add(this);
        return;
    }

    @Override
    public Term substitute(Var v, Term t) {
        return (equals(v)? t : this);
    }

    @Override
    public Term substitute(Map<Var, Term> sub) {
        return sub.getOrDefault(this, this);
    }

    @Override
    Pair<Term, Integer> distinctVarH(String id, int acc) {
        return new Pair<>(this, acc);
    }
}
