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

import fortress.lambda.visitor.TermVisitor;
import fortress.util.Pair;

import java.util.*;

import static fortress.lambda.Type.mkFnTy;
import static fortress.util.Errors.failIf;

/**
 * Created by amirhossein on 14/01/16.
 */
public final class Abs extends Term {

    private Var arg;
    private Term fun;

    public Abs(Var arg, Term fun){
        failIf(arg == null );
        failIf(fun == null );
        this.fun = fun;
        this.arg = arg;
        this.ty = mkFnTy(arg.ty, fun.ty);
    }

    public static Abs mkAbs(List<Var> args, Term fun){
        failIf(args.size() < 1);
        Abs result = new Abs(args.get(args.size() - 1), fun);
        for (int i = args.size() - 2; i >= 0; i--)
            result = new Abs(args.get(i), result);
        return result;
    }

    public Var getArg(){
        return arg;
    }

    public Term getFun(){
        return fun;
    }

    @Override
    public boolean isVar() {
        return false;
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
        return true;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append('[');
        Pair<List<Var>, Term> p = brkAbs();
        Iterator<Var> it = p.left.iterator();
        Var v = it.next();
        String tyName = v.ty.toString();
        sb.append(v.getName());
        sb.append(':');
        sb.append(tyName);
        while (it.hasNext()){
            v = it.next();
            sb.append(", ");
            sb.append(v.getName());
            sb.append(':');
            sb.append(tyName);
        }
        sb.append(". ");
        sb.append(p.right.toString());
        sb.append(']');
        return sb.toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Abs other = (Abs) obj;
        if (!fun.equals(other.fun))
            return false;
        return arg.equals(other.arg);
    }

    @Override
    public int compareTo(Term o) {
        failIf(o == null);
        if (getClass() != o.getClass())
            return 1;
        Abs other = (Abs) o;
        if (fun.compareTo(other.fun) != 0)
            return fun.compareTo(other.fun);
        return arg.compareTo(other.arg);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + fun.hashCode();
        result = prime * result + arg.hashCode();
        return result;
    }

    @Override
    public <T> T accept(TermVisitor<T> v) {
        return v.visitAbs(this);
    }

    @Override
    protected void constantsH(Set<Con> acc){
        fun.constantsH(acc);
        return;
    }

    @Override
    protected void typeFunctorsH(Set<Pair<String, Integer>> acc){
        fun.typeFunctorsH(acc);
        arg.typeFunctorsH(acc);
    }

    @Override
    protected void fvH(Set<Var> acc){
        fun.fvH(acc);
        acc.remove(arg);
        return;
    }

    @Override
    public Term substitute(Var v, Term t) {
        return (v.equals(arg) || t.fv().contains(arg)? this: new Abs(arg, fun.substitute(v, t)));
    }

    @Override
    public Term substitute(Map<Var, Term> sub) {
        Map<Var, Term> allowedSub = new HashMap<>();
        for (Map.Entry<Var, Term> e: sub.entrySet()) {
            if (e.getKey().equals(arg) || e.getValue().fv().contains(arg))
                continue;
            allowedSub.put(e.getKey(), e.getValue());
        }
        return new Abs(arg, fun.substitute(allowedSub));
    }

    @Override
    Pair<Term, Integer> distinctVarH(String id, int acc) {
        Var v = new Var(id + Integer.toString(acc), arg.ty);
        Pair<Term, Integer> p = fun.substitute(arg, v).distinctVarH(id, acc + 1);
        return new Pair<>(new Abs(v, p.left), p.right);
    }

}
