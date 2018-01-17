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
import fortress.fol.Arith;
import fortress.fol.FOL;
import fortress.lambda.Con;
import fortress.lambda.Term;
import fortress.lambda.Type;
import fortress.lambda.Var;
import fortress.util.Pair;

import java.util.*;

/**
 * Created by Amirhossein Vakili.
 */
public class Theory {

    public final String name;
    private final Optional<Theory> base;
    public Set<Pair<String, Integer>> functorSet;
    public Set<Con> constantSet;
    public Map<String, Definition> defSet;
    public List<String> defSetOrder;
    public Set<Term> axiomSet;

    public static final Theory BASE_THEORY = createBase();

    public static final Theory FOL_THEORY = createFOL();

    public static final Theory ARITH_THEORY = createArith();

    public Theory(String name){
        this.name = name;
        base = Optional.empty();
        functorSet = new HashSet<>();
        constantSet = new HashSet<>();
        defSet = new HashMap<>();
        defSetOrder = new ArrayList<>();
        axiomSet = new HashSet<>();
    }

    public Theory(String name, Theory base){
        this.name = name;
        this.base = Optional.of(base);
        functorSet = new HashSet<>();
        constantSet = new HashSet<>();
        defSet = new HashMap<>();
        defSetOrder = new ArrayList<>();
        axiomSet = new HashSet<>();
    }

    private static Theory createBase(){
        Theory result = new Theory("base_theory");
        result.functorSet.add(new Pair<>(Constants.FN_Str, 2));
        result.functorSet.add(new Pair<>(Constants.BOOL_Str, 0));
        result.constantSet.add(Term.EQ);
        return result;
    }

    private static Theory createFOL(){
        Theory result = new Theory("fol_theory", BASE_THEORY);
        result.addCon(FOL.true_);
        result.addCon(FOL.false_);
        result.addCon(FOL.not);
        result.addCon(FOL.and);
        result.addCon(FOL.or);
        result.addCon(FOL.imp);
        result.addCon(FOL.iff);
        result.addCon(FOL.forall);
        result.addCon(FOL.exists);
        return result;
    }

    private static Theory createArith(){
        Theory result = new Theory("arith_theory", FOL_THEORY);
        result.functorSet.add(new Pair<>(Constants.INTEGER_Str, 0));
        result.addFunctor(Constants.INTEGER_Str, 0);
        result.addCon(Arith.abs);
        result.addCon(Arith.add);
        result.addCon(Arith.sub);
        result.addCon(Arith.mul);
        result.addCon(Arith.div);
        result.addCon(Arith.mod);
        result.addCon(Arith.less);
        result.addCon(Arith.greater);
        result.addCon(Arith.lessEq);
        result.addCon(Arith.greaterEq);
        return result;
    }

    @Override
    public String toString(){
        final String tab = "    ";
        String result = "THEORY " + name + ":\r\n";
        result = result + tab + "Functors:\r\n" + tab + tab + functorSet.toString() + "\r\n";
        result = result + tab + "Constants:\r\n";
        for (Con c: constantSet)
            result = result + tab + tab + c.toString() + " : " + c.getType().toString() + "\r\n";
        result = result + tab + "Definitions:\r\n";
        for (String defName: defSetOrder)
            result = result + tab + tab + defSet.get(defName).toString();
        result = result + tab + "Axioms:\r\n";
        for (Term t: axiomSet)
            result = result + tab + tab + t.toString() + "\r\n";
        return result;
    }

    public Optional<Term> getTermByName(String name){
        for (Con c: constantSet)
            if (c.getName().equals(name))
                return Optional.of(c);
        if (defSet.containsKey(name))
            return Optional.of(defSet.get(name).defAsVar);
        if (base.isPresent())
            return base.get().getTermByName(name);
        return Optional.empty();
    }

    public Theory getBaseTheory(){
        return base.get();
    }

    public void print(int l){
        System.out.println(this);
        if (l > 0 && base.isPresent())
            base.get().print(l - 1);
        return;
    }

    public void printAll(){
        System.out.println(this);
        if (base.isPresent())
            base.get().printAll();
    }

    /*
    private void pushToBase(){
        if (base.isPresent()){
            Theory temp = base.get();
            temp.functorSet.addAll(functorSet);
            temp.constantSet.addAll(constantSet);
            for (String defName: defSetOrder) {
                temp.defSet.put(defName, defSet.get(defName));
                temp.defSetOrder.add(defName);
            }
            temp.axiomSet.addAll(axiomSet);

        } else {
            this.base = Optional.of(this);
        }
        //Time clean up :)
        functorSet = new HashSet<>();
        constantSet = new HashSet<>();
        defSet = new HashMap<>();
        defSetOrder = new ArrayList<>();
        axiomSet = new HashSet<>();
    }
    */

    public boolean isInBase(Pair<String, Integer> functor){
        if (!base.isPresent())
            return false;
        if (base.get().functorSet.contains(functor))
            return true;
        return base.get().isInBase(functor);
    }

    public boolean addFunctor(String functor, Integer arity){
        //Some checks need to be done.
        Pair<String, Integer> temp = new Pair<>(functor, arity);
        if (isInBase(temp))
                return false;
        functorSet.add(temp);
        return true;
    }

    public boolean isInBase(Con c){
        if (c.getName().matches("[0-9]+"))
            return true;
        if (!base.isPresent())
            return false;
        if (base.get().constantSet.contains(c))
            return true;
        return base.get().isInBase(c);
    }

    public boolean addCon(Con c){
        // some checks need to be done.
        if (isInBase(c))
            return false;
        for (Pair<String, Integer> si: c.getType().functors())
            if (!isInBase(si))
                functorSet.add(si);
        constantSet.add(c);
        return true;
    }

    public boolean isDefNameInBase(String name){
        if (!base.isPresent())
            return false;
        if (base.get().defSetOrder.contains(name))
            return true;
        return base.get().isDefNameInBase(name);
    }

    public Var addDef(String name, Term body, Var...args){
        //some checks need to be done.
        if (isDefNameInBase(name))
            return new Var(name, body.getType());
        Definition temp = new Definition(name, body, args);
        defSet.put(name, temp);
        defSetOrder.add(name);
        for (Con c: body.constantSet())
            addCon(c);
        for (Pair<String, Integer> si: body.typeFunctorSet())
            addFunctor(si.left, si.right);
        for (Var v: args)
            for(Pair<String, Integer> si: v.getType().functors())
                addFunctor(si.left, si.right);
        return temp.defAsVar;
    }

    public boolean isAxiomInBase(Term t){
        if (!base.isPresent())
            return false;
        if (base.get().axiomSet.contains(t))
            return true;
        return base.get().isAxiomInBase(t);
    }
    public boolean addAxiom(Term t){
        //System.out.println(t);
        if (!t.getType().equals(Type.BOOL) || !t.isClosed())
            return false;
        if (isAxiomInBase(t))
            return false;
        axiomSet.add(t);
        for (Con c: t.constantSet())
            addCon(c);
        for (Pair<String, Integer> si: t.typeFunctorSet())
            addFunctor(si.left, si.right);
        return true;
    }

    public boolean addAxiom(String term){
        return addAxiom(Parser.termOfString(this, term));
    }

    public Term parse(String term){
        return Parser.termOfString(this, term);
    }

    /*
    * term ::= iff_term
    *
    * iff_term ::= imp_term
    *            | imp_term IFF iff_term
    *
    * imp_term ::= or_term
    *            | or_term IMP imp_term
    *
    * or_term ::= and_term
    *           | and_term OR or_term
    *
    * and_term ::= not_term
    *            | not_term AND and_term
    *
    * not_term ::= eq_term
    *            | NOT not_term
    *
    * eq_term ::= add_sub_term
    *           | add_sub_term EQ add_sub_term
    *
    * add_sub_term ::= mul_div_term
    *                | mul_div_term ADD_SUB add_sub_term
    *
    * mul_div_term ::= neg_term
    *                | neg_term MUL_DIV mul_div_term
    *
    * neg_term ::= app
    *
    *
    *
    *
    *
    *
    */
}