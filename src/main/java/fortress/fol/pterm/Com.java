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

package fortress.fol.pterm;

import fortress.fol.pterm.visitor.PTermVisitor;
import fortress.util.Pair;

import java.util.*;
import java.util.stream.Collectors;

import static fortress.util.Errors.failIf;
import static fortress.util.ListOps.compareList;
import static fortress.util.ListOps.exists;


public final class Com extends PTerm {
    
    private String functor;
    private List<PTerm> args;
    
    public Com(String functor, List<PTerm> args){
        failIf(functor == null);
        failIf(exists(t -> t == null, args));
        this.functor = functor;
        this.args = args;
    }
    

    public String getFunctor(){
        return functor;
    }

    public List<PTerm> getArgs(){
        return args;
    }


    @Override
    public boolean isPVar(){
        return false;
    }

    @Override
    public boolean isCon(){
        return args.size() == 0;
    }

    @Override
    public boolean isCom(){
        return true;
    }

    @Override
    public String toString() {
        String argsStr = args.toString();
        if(args.size() == 0)
            argsStr = "";
        return functor + argsStr;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + args.hashCode();
        result = prime * result + functor.hashCode();
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        Com other = (Com) obj;
        if (!functor.equals(other.functor))
            return false;
        return args.equals(other.args);
    }
    
    @Override
    public <T> T accept(PTermVisitor<T> v){
        return v.visitCom(this);
    }
    
    @Override
    public int compareTo(PTerm t){
        failIf(t == null);
        if(this == t)
            return 0;
        if(getClass() != t.getClass())
            return 1;
        Com other = (Com) t;
        if(functor.compareTo(other.functor) != 0)
            return functor.compareTo(other.functor);
        return compareList(args, other.args);
    }

    @Override
    public PTerm substitute(PVar v, PTerm t){
        return new Com(functor, args.stream().map(tt -> tt.substitute(v, t)).collect(Collectors.toList()));
    }

    @Override
    public PTerm substitute(Map<PVar, PTerm> sub){
        return new Com(functor, args.stream().map(t -> t.substitute(sub)).collect(Collectors.toList()));
    }

    @Override
    public Map<PVar, PTerm> unify(PTerm other){
        if(other.equals(this))
            return new HashMap<>();
        List<Pair<PTerm, PTerm>> eqs = new ArrayList<>();
        eqs.add(new Pair<>(this, other));
        return PTerm.unify(eqs);
    }
    
    @Override
    protected void varsHelper(Set<PVar> acc){
        for(PTerm t: args)
            t.varsHelper(acc);
    }

    @Override
    protected void functorsH(Set<Pair<String, Integer>> acc){
        acc.add(new Pair<>(functor, args.size()));
        for(PTerm t: args)
            t.functorsH(acc);
    }
}
