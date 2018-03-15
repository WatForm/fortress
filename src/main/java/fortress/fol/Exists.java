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
import fortress.fol.pterm.Com;
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
public class Exists extends Formula {

    private SortedSet<Var> vars;
    private Formula body;

    public Exists(SortedSet<Var> vars, Formula body){
        failIf(vars == null);
        failIf(body == null);
        failIf(vars.isEmpty());
        this.vars = vars;
        this.body = body;
    }

    public SortedSet<Var> getVars(){
        return vars;
    }

    public Formula getBody(){
        return body;
    }

    @Override
    public boolean is_quantifier_free() {
        return false;
    }

    @Override
    public boolean isExists() {
        return true;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(Constants.EXISTS_Str);
        Iterator<Var> it = vars.iterator();
        Var v = it.next();
        sb.append('[');
        sb.append(v.getName());
        sb.append(':');
        sb.append(v.getType().toString());
        while (it.hasNext()){
            sb.append(", ");
            v = it.next();
            sb.append(v.getName());
            sb.append(':');
            sb.append(v.getType().toString());
        }
        sb.append(". ");
        sb.append(body.toString());
        sb.append(']');
        return  sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (o == this)
            return true;
        if (o == null)
            return false;
        if (getClass() != o.getClass())
            return false;
        Exists temp = ((Exists) o);
        return body.equals(temp.body) && vars.equals(temp.vars);
    }

    @Override
    public int compareTo(Formula o) {
        failIf(o == null);
        if (o == this)
            return 0;
        if (getClass() != o.getClass())
            return 1;
        Exists temp = ((Exists) o);
        int test = vars.size() - temp.vars.size();
        if (test != 0)
            return test;
        test = body.compareTo(temp.body);
        if (test != 0)
            return test;
        Iterator<Var> it1 = vars.iterator();
        Iterator<Var> it2 = temp.vars.iterator();
        while (it1.hasNext() && it2.hasNext()){
            Var v1 = it1.next();
            Var v2 = it2.next();
            test = v1.compareTo(v2);
            if (test != 0)
                return test;
        }
        if (it1.hasNext())
            return 1;
        if (it2.hasNext())
            return -1;
        return 0;
    }

    @Override
    public int hashCode() {
        final int prime = 37;
        int result = 1;
        result = prime * result + vars.hashCode();
        result = prime * result + body.hashCode();
        return result;
    }

    @Override
    public <T> T accept(FormulaVisitor<T> v){
        return v.visitExists(this);
    }

    @Override
    public SExpr toSMTLIB(){
        List<SExpr> temp = new ArrayList<>();
        temp.add(new StrExpr(Constants.smtlibOf.getOrDefault(Constants.EXISTS_Str, Constants.EXISTS_Str)));
        List<SExpr> vs = new ArrayList<>();
        for (Var v: vars)
            vs.add(new ComExpr(new StrExpr(v.getName()),
                               new StrExpr(Constants.smtlibOf.getOrDefault(v.getType().toString(),
                                                                           v.getType().toString()))));
        temp.add(new ComExpr(vs));
        temp.add(body.toSMTLIB());
        return new ComExpr(temp);
    }

    @Override
    void fvH(Set<Var> acc) {
        body.fvH(acc);
        for(Var v: vars)
            acc.remove(v);
    }

    @Override
    public Formula substitute(Var v, Term t) {
        if (vars.contains(v))
            return this;
        for (Var vv: t.fv())
            if (vars.contains(vv))
                return this;
        return new Exists(vars, body.substitute(v, t));
    }

    @Override
    public Formula substitute(Map<Var, Term> sub) {
        for (Map.Entry<Var, Term> e: sub.entrySet()){
            if (vars.contains(e.getKey()))
                return this;
            for (Var v: e.getValue().fv())
                if (vars.contains(v))
                    return this;
        }
        return new Exists(vars, body.substitute(sub));
    }

    @Override
    public Formula nnf(){
        return new Exists(vars, body.nnf());
    }

    @Override
    Formula simplify1(){
        if (body.equals(true_) || body.equals(false_))
            return body;
        if (body.isExists()){
            vars.addAll(((Exists) body).vars);
            return new Exists(vars, ((Exists) body).body);
        }
        return new Exists(vars, body);
    }

    @Override
    public Formula simplify(){
        return new Exists(vars, body.simplify()).simplify1();
    }

    @Override
    Pair<Formula, Integer> skolemizeH(int acc, List<Term> argumentList, List<PTerm> typeList, List<Const> skolemFunList) {
        Formula temp = body;
        int j = acc;
        for(Var v: vars){
            PTerm type = v.getType();
            for (int i = typeList.size() - 1; i >= 0; i--)
                type = new Com(Constants.FN_Str, new ArrayList<>(Arrays.asList(typeList.get(i), type)));
            Const skolem = new Const("_skolem" + Integer.toString(j++), type);
            skolemFunList.add(skolem);
            Term tt = argumentList.isEmpty()? skolem : FOL.apply(skolem, argumentList);
            temp = temp.substitute(v, tt);
        }
        return temp.skolemizeH(j, argumentList, typeList, skolemFunList);
    }

    @Override
    public Formula prenex() {
        body = body.prenex();
        if (body.isExists()) {
            vars.addAll(((Exists) body).getVars());
            body = ((Exists) body).body;
        }
        return this;
    }
}
