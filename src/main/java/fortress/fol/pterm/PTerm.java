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

import static fortress.util.Errors.failIf;



/**
* PTerm represents a Type, for example Int or Int -&gt;g Bool.
*/
public abstract class PTerm implements Comparable<PTerm>{
    
    public abstract boolean isPVar();

    public abstract boolean isCon();

    public abstract boolean isCom();

    @Override
    public abstract String toString();
    
    @Override
    public abstract boolean equals(Object obj);
    
    @Override
    public abstract int hashCode();
    
    public abstract <T> T accept(PTermVisitor<T> v);

    /**
    * Replace a type variable with another type.
    * @param v      The type variable to replace.
    * @param t      The type with which to replace the variable.
    * @return       A new type with the variable substituted with the other type.
    */
    public abstract PTerm substitute(PVar v, PTerm t);

    /**
    * Replace several type varaibles with other types.
    * @param sub    A map from type variables to types indicating substiutions.
    * @return       A new type with the substiutions applied.
    */
    public abstract PTerm substitute(Map<PVar, PTerm> sub);

    public abstract  Map<PVar, PTerm> unify(PTerm other);
    
    protected abstract void varsHelper(Set<PVar> acc);
    
    /**
    * Collects all type variables contained within the type.
    */
    public Set<PVar> vars(){
        Set<PVar> result = new HashSet<>();
        this.varsHelper(result);
        return result;
    }

    protected abstract void functorsH(Set<Pair<String, Integer>> acc);

    public Set<Pair<String, Integer>> functors(){
        Set<Pair<String, Integer>> result = new HashSet<>();
        this.functorsH(result);
        return result;
    }

    private static void unifyH(Map<PVar, PTerm> env,
                               Set<Pair<PVar, PVar>> tc,
                               List<Pair<PTerm, PTerm>> eqs, int index){
        if(eqs.size() <= index)
            return;
        PTerm t1 = eqs.get(index).left;
        PTerm t2 = eqs.get(index).right;
        if(t1.isCom() && t2.isCom()){
            failIf(!((Com) t1).getFunctor().equals(((Com) t2).getFunctor()));
            final int len = ((Com) t1).getArgs().size();
            failIf(len != ((Com) t2).getArgs().size());
            for(int i = 0; i != len; ++i)
                eqs.add(new Pair<>(((Com)t1).getArgs().get(i),((Com) t2).getArgs().get(i)));
            unifyH(env, tc, eqs, index + 1);
            return;
        }
        PVar v;
        PTerm t;
        if(t1.isPVar()){
            v = (PVar) t1;
            t = t2;
        } else{
            v = (PVar) t2;
            t = t1;
        }
        if(env.containsKey(v)){
            eqs.add(new Pair<>(env.get(v), t));
            unifyH(env, tc, eqs, index + 1);
        }
        if(v.equals(t)){
            unifyH(env, tc, eqs, index + 1);
            return;
        }
        Set<PVar> vars = t.vars();
        for(PVar vp: vars) {
            failIf(v.equals(vp));
            failIf(tc.contains(new Pair<>(vp, v)));
            tc.add(new Pair<>(v, vp));
            Set<Pair<PVar, PVar>> newEdges = new HashSet<>();
            for (Pair<PVar, PVar> xv : tc)
                if (xv.right.equals(v))
                    newEdges.add(new Pair<>(xv.left, vp));
            tc.addAll(newEdges);
        }
        PTerm tp = t.substitute(env);
        for(Map.Entry<PVar, PTerm> entry: env.entrySet())
            env.put(entry.getKey() , entry.getValue().substitute(v, tp));
        env.put(v, tp);
        unifyH(env, tc, eqs, index + 1);
        return;
    }

    /**
    * Compute a substitution that unifies (makes true) a list of type equations.
    * @param eqs    A list of equations (represented as pairs).
    * @return       A substitution that unifies each of the given equations.
    */
    public static Map<PVar, PTerm> unify(List<Pair<PTerm, PTerm>> eqs){
        Map<PVar, PTerm> sub = new HashMap<>();
        Set<Pair<PVar, PVar>> tc = new HashSet<>();

        unifyH(sub, tc, eqs, 0);
        return  sub;

    }
}
