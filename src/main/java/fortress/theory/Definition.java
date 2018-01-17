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

package fortress.theory;

import fortress.Constants;
import fortress.fol.Formula;
import fortress.lambda.Term;
import fortress.lambda.Type;
import fortress.lambda.Var;
import fortress.formats.smt.smtlib.ComExpr;
import fortress.formats.smt.smtlib.SExpr;
import fortress.formats.smt.smtlib.StrExpr;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static fortress.util.Errors.failIf;
import static fortress.util.ListOps.exists;

/*u*
 * Created by Amirhossein Vakili.
 */
public class Definition {
    public final String name;
    public final List<Var> args;
    public final Term body;
    public final Var defAsVar;

    public Definition(String name, Term body, List<Var> args){
        failIf(name == null);
        failIf(args == null);
        failIf(body == null);
        failIf(exists((v) -> v == null, args));
        this.name = name;
        this.args = args;
        this.body = body;
        defAsVar = new Var(name, body.getType());
    }

    public Definition(String name, Term body, Var... args){
        failIf(name == null);
        failIf(args == null);
        failIf(body == null);
        this.args = Arrays.asList(args);
        failIf(exists((v) -> v == null, this.args));
        this.name = name;
        this.body = body;
        defAsVar = new Var(name, body.getType());
    }

    @Override
    public String toString(){
        String result = "def " + name ;
        if(args.isEmpty())
            return result + " : " + body.getType().toString() + " {" + body.toString() + "}";
        return result + args.toString() + " : " + body.getType().toString() + " {" + body.toString() + "}";
    }


    @Override
    public boolean equals(Object o){
        if(o == null)
            return false;
        if(o == this)
            return true;
        if(getClass() != o.getClass())
            return false;
        Definition other = (Definition) o;
        return name.equals(other.name) && body.equals(other.body) && args.equals(other.args);
    }

    @Override
    public int hashCode(){
        final int prime = 31;
        int result = 1;
        result = result * prime + name.hashCode();
        result = result * prime + args.hashCode();
        result = result * prime + body.hashCode();
        return result;
    }

    public SExpr toSMTLIB(){
        List<SExpr> temp = new ArrayList<>();
        temp.add(new StrExpr("define-fun"));
        temp.add(new StrExpr(name));
        List<SExpr> al = new ArrayList<>();
        for (Var v: args)
            al.add(new ComExpr(new StrExpr(v.getName()),
                               new StrExpr(Constants.smtlibOf.getOrDefault(v.getType().toString(),
                                                                           v.getType().toString()))));
        temp.add(new ComExpr(al));
        if (body.getType().equals(Type.BOOL))
            temp.add(Formula.fromTerm(body).toSMTLIB());
        else
            temp.add(body.toSMTLIB());
        return new ComExpr(temp);
    }
}
