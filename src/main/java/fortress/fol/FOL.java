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
import fortress.lambda.*;
import fortress.util.Pair;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

import static fortress.util.Errors.failIf;


/**
 * Created by amirhossein on 14/01/16.
 */
public final class FOL {

    public static Com bool = fortress.lambda.Type.BOOL;

    private FOL(){}

    public static Com mkSort(String name){
        return new Com(name, new ArrayList<>());
    }

    public static Con mkProp(String name){
        return new Con(name, bool);
    }

    public static Var mkVar(String name, PTerm ty){
        return new Var(name, ty);
    }

    public static Con mkFun(String name, PTerm... tyList){
        if (tyList.length == 1)
            return new Con(name, tyList[0]);
        return new Con(name, Type.mkFnTy(tyList));
    }

    public static App apply(Term... args){
        return App.mkApp(args);
    }

    public static App apply(Con f, List<Term> args){
        return App.mkApp(f, args);
    }

    public static Function<List<Term>, App> mkFunApply(String name, PTerm... tyList){
        failIf(tyList.length <= 1);
        return (a) -> apply(mkFun(name, tyList), a);
    }

    public static Function<Term[], App> mkFunApplyArray(String name, PTerm... tyList){
        failIf(tyList.length <= 1);
        return (a) -> apply(mkFun(name, tyList), Arrays.asList(a));
    }

    public static boolean isEq(Term t){
        return t.isEq();
    }

    public static App mkEq(Term t1, Term t2){
        return Term.mkEq(t1, t2);
    }

    public static Pair<Term, Term> brkEq(Term t){
        return t.brkEq();
    }

    public static Con false_ = mkProp(Constants.FALSE_Str);

    public static boolean isFalse(Term t){
        return t.equals(false_);
    }

    public static Con true_ = mkProp(Constants.TRUE_Str);

    public static boolean isTrue(Term t){
        return t.equals(true_);
    }

    public static Con not = mkFun(Constants.NOT_Str, Type.mkFnTy(bool, bool));

    public static boolean isNot(Term t){
        return t.isApp() && ((App) t).getFun().equals(not);
    }

    public static App mkNot(Term t){
        //return apply(not, t);
        return new App(not, t);
    }

    public static Term brkNot(Term t){
        failIf(!isNot(t));
        return (((App) t).getArg());
    }

    private static PTerm bool3 = Type.mkFnTy(bool, bool, bool);

    // AND

    public static Con and = mkFun(Constants.AND_Str, bool3);

    public static boolean isAnd(Term t){
        if (!t.isApp())
            return false;
        Term temp = ((App) t).getFun();
        return temp.isApp() && ((App) temp).getFun().equals(and);
    }

    public static App mkAnd(Term t1, Term t2){
        //return apply(and, t1, t2);
        return new App(new App(and, t1), t2);
    }

    public static App mkAnd(List<Term> tl){
        failIf(tl.size() < 2);
        App result = mkAnd(tl.get(0), tl.get(1));
        for (int i = 2; i < tl.size(); i++)
            result = mkAnd(result, tl.get(i));
        return result;
    }

    public static Pair<Term, Term> brkAnd(Term t){
        failIf(!isAnd(t));
        App temp = (App) t;
        return new Pair<>(((App) temp.getFun()).getArg(), temp.getArg());
    }

    private static void brkAnd(Term t, List<Term> acc){
        if (!isAnd(t)) {
            acc.add(t);
            return;
        }
        Pair<Term, Term> tt = brkAnd(t);
        brkAnd(tt.left, acc);
        brkAnd(tt.right, acc);
    }

    public static List<Term> brkAnds(Term t){
        List<Term> result = new ArrayList<>();
        brkAnd(t, result);
        return result;
    }

    // OR

    public static Con or = mkFun(Constants.OR_Str, bool3);

    public static boolean isOr(Term t){
        if (!t.isApp())
            return false;
        Term temp = ((App) t).getFun();
        return temp.isApp() && ((App) temp).getFun().equals(or);
    }

    public static App mkOr(Term t1, Term t2){
        //return apply(or, t1, t2);
        return new App(new App(or, t1), t2);
    }

    public static App mkOr(List<Term> tl){
        failIf(tl.size() < 2);
        App result = mkOr(tl.get(0), tl.get(1));
        for (int i = 2; i < tl.size(); i++)
            result = mkOr(result, tl.get(i));
        return result;
    }

    public static Pair<Term, Term> brkOr(Term t){
        failIf(!isOr(t));
        App temp = (App) t;
        return new Pair<>(((App) temp.getFun()).getArg(), temp.getArg());
    }

    private static void brkOr(Term t, List<Term> acc){
        if (!isOr(t)) {
            acc.add(t);
            return;
        }
        Pair<Term, Term> tt = brkOr(t);
        brkOr(tt.left, acc);
        brkOr(tt.right, acc);
    }

    public static List<Term> brkOrs(Term t){
        List<Term> result = new ArrayList<>();
        brkOr(t, result);
        return result;
    }

    // IMP

    public static Con imp = mkFun(Constants.IMP_Str, bool3);

    public static boolean isImp(Term t){
        if (!t.isApp())
            return false;
        Term temp = ((App) t).getFun();
        return temp.isApp() && ((App) temp).getFun().equals(imp);
    }

    public static App mkImp(Term t1, Term t2){
        //return apply(imp, t1, t2);
        return new App(new App(imp, t1), t2);
    }

    public static Pair<Term, Term> brkImp(Term t){
        failIf(!isImp(t));
        App temp = (App) t;
        return new Pair<>(((App) temp.getFun()).getArg(), temp.getArg());
    }

    // IFF

    public static Con iff = mkFun(Constants.IFF_Str, bool3);

    public static boolean isIff(Term t){
        if (!t.isApp())
            return false;
        Term temp = ((App) t).getFun();
        return temp.isApp() && ((App) temp).getFun().equals(iff);
    }

    public static App mkIff(Term t1, Term t2){
        //return apply(iff, t1, t2);
        return new App(new App(iff, t1), t2);
    }

    public static Pair<Term, Term> brkIff(Term t){
        failIf(!isIff(t));
        App temp = (App) t;
        return new Pair<>(((App) temp.getFun()).getArg(), temp.getArg());
    }

    // FORALL

    public static Con forall = mkFun(Constants.FORALL_Str, Type.mkFnTy(Type.mkFnTy(Type._a, bool), bool));

    public static boolean isForall(Term t){
        return t.isApp() && ((App) t).getFun().equals(forall);
    }

    public static App mkForall(Var v, Term t){
        return new App(forall, new Abs(v, t));
    }

    public static App mkForall(List<Var> vl, Term t){
        failIf(vl.size() < 1);
        App result = mkForall(vl.get(vl.size() - 1), t);
        for (int i = vl.size() - 2; i >= 0; i--)
            result = mkForall(vl.get(i), result);
        return result;
    }

    public static Pair<Var, Term> brkForall(Term t){
        failIf(!isForall(t));
        Abs temp = (Abs) ((App) t).getArg();
        return new Pair<>(temp.getArg(), temp.getFun());
    }

    public static Pair<List<Var>, Term> brkForalls(Term t){
        List<Var> vars = new ArrayList<>();
        Term fun = t;
        while (isForall(fun)){
            Pair<Var, Term> temp = brkForall(fun);
            vars.add(temp.left);
            fun = temp.right;
        }
        return new Pair<>(vars, fun);
    }

    // EXISTS

    public static Con exists = mkFun(Constants.EXISTS_Str, Type.mkFnTy(Type.mkFnTy(Type._a, bool), bool));

    public static boolean isExists(Term t){
        return t.isApp() && ((App) t).getFun().equals(exists);
    }

    public static App mkExists(Var v, Term t){
        return new App(exists, new Abs(v, t));
    }

    public static App mkExists(List<Var> vl, Term t){
        failIf(vl.size() < 1);
        App result = mkExists(vl.get(vl.size() - 1), t);
        for (int i = vl.size() - 2; i >= 0; i--)
            result = mkExists(vl.get(i), result);
        return result;
    }

    public static Pair<Var, Term> brkExists(Term t){
        failIf(!isExists(t));
        Abs temp = (Abs) ((App) t).getArg();
        return new Pair<>(temp.getArg(), temp.getFun());
    }

    public static Pair<List<Var>, Term> brkExistss(Term t){
        List<Var> vars = new ArrayList<>();
        Term fun = t;
        while (isExists(fun)){
            Pair<Var, Term> temp = brkExists(fun);
            vars.add(temp.left);
            fun = temp.right;
        }
        return new Pair<>(vars, fun);
    }


}
