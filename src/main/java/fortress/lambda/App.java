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


import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static fortress.util.Errors.failIf;


/**
 * Created by amirhossein on 14/01/16.
 */
public final class App extends Term {

    private Term fun;
    private Term arg;

    public App(Term fun, Term arg){
        failIf(fun == null);
        failIf(arg == null);
        Pair<PTerm, PTerm> temp = Type.brkFnTy(fun.ty);
        this.fun = fun;
        this.arg = arg;
        this.ty = temp.right.substitute(temp.left.unify(arg.ty));
    }

    public static App mkApp(Term... args){
        failIf(args.length < 2);
        App result = new App(args[0], args[1]);
        for (int i = 2; i < args.length; i++)
            result = new App(result, args[i]);
        return result;
    }

    public static App mkApp(Term fun, List<Term> args){
        failIf(args.size() < 1);
        App result = new App(fun, args.get(0));
        for (int i = 1; i != args.size(); i++)
            result = new App(result, args.get(i));
        return result;
    }

    public static Term mkApp(List<Term> terms){
        failIf(terms.isEmpty());
        Iterator<Term> it = terms.iterator();
        Term result = it.next();
        while (it.hasNext())
            result = new App(result, it.next());
        return result;
    }

    public Term getFun(){
        return fun;
    }

    public Term getArg(){
        return arg;
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
        return true;
    }

    @Override
    public boolean isAbs() {
        return false;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        List<Term> termList = this.brkApp();
        boolean flag = (termList.size() != 2) || !termList.get(1).isAbs();
        Iterator<Term> it = termList.iterator();
        sb.append(it.next().toString());
        if (flag)
            sb.append('[');
        sb.append(it.next().toString());
        while (it.hasNext()){
            sb.append(", ");
            sb.append(it.next().toString());
        }
        if (flag)
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
        App other = (App) obj;
        if (!fun.equals(other.fun))
            return false;
        return arg.equals(other.arg);
    }

    @Override
    public int compareTo(Term o) {
        failIf(o == null);
        if (o.getClass() == Var.class || o.getClass() == Con.class)
            return 1;
        if (getClass() != o.getClass())
            return -1;
        App other = (App) o;
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
        return v.visitApp(this);
    }

    @Override
    protected void constantsH(Set<Con> acc){
        fun.constantsH(acc);
        arg.constantsH(acc);
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
        arg.fvH(acc);
        return;
    }

    @Override
    public Term substitute(Var v, Term t) {
        return new App(fun.substitute(v, t), arg.substitute(v, t));
    }

    @Override
    public Term substitute(Map<Var, Term> sub) {
        return new App(fun.substitute(sub), arg.substitute(sub));
    }

    @Override
    Pair<Term, Integer> distinctVarH(String id, int acc) {
        Pair<Term, Integer> p1 = fun.distinctVarH(id, acc);
        Pair<Term, Integer> p2 = arg.distinctVarH(id, p1.right);
        return new Pair<>(new App(p1.left, p2.left), p2.right);
    }

}
