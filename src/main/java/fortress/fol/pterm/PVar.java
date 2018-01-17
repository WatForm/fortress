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

//import java.util.ArrayList;
import fortress.fol.pterm.visitor.PTermVisitor;
import fortress.util.Pair;

import java.util.*;

import static fortress.util.Errors.failIf;


public final class PVar extends PTerm {
    
    private String name;
    
    public PVar(String name){
        failIf(name == null);
        this.name = name;
    }
    
    public String getName(){
        return name;
    }

    @Override
    public boolean isPVar(){
        return true;
    }

    @Override
    public boolean isCon(){return false;}

    @Override
    public boolean isCom(){
        return false;
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        return name.equals(((PVar) obj).name);
    }

    @Override
    public int compareTo(PTerm t) {
        failIf(t == null);
        if (this == t)
            return 0;
        if (getClass() != t.getClass())
            return -1;
        return name.compareTo(((PVar) t).name);
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }
    
    @Override
    public <T> T accept(PTermVisitor<T> v){
        return v.visitPVar(this);
    }

    @Override
    public PTerm substitute(PVar v, PTerm t){
        if (v.equals(this))
            return t;
        return this;
    }

    @Override
    public PTerm substitute(Map<PVar, PTerm> sub){
        return sub.getOrDefault(this, this);
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
        acc.add(this);
    }

    @Override
    protected void functorsH(Set<Pair<String, Integer>> acc){
        return;
    }
}