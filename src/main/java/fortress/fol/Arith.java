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
import fortress.lambda.App;
import fortress.lambda.Const;
import fortress.lambda.Term;

import fortress.util.Pair;

/**
 * Created by Amirhossein Vakili.
 */
public final class Arith {

    private Arith(){}

    public static final Com int_ = FOL.mkSort(Constants.INTEGER_Str);

    public static Const numeral(int n){
        return new Const(Integer.toString(n), int_);
    }

    public static final Const zero = numeral(0);

    public static final Const one = numeral(1);

    // abs
    public static final Const abs = FOL.mkFun(Constants.ABS_Str, int_, int_);

    public static boolean isAbs(Term t){
        return t.isUnary(abs);
    }

    public static App mkAbs(Term t){
        return Term.mkUnary(add, t);
    }

    public static Term brkAbs(Term t){
        return t.brkUnary(abs);
    }

    // add
    public static final Const add = FOL.mkFun(Constants.ADD_Str, int_, int_, int_);

    public static boolean isAdd(Term t){
        return t.isBinary(add);
    }

    public static App mkAdd(Term t1, Term t2){
        return Term.mkBinary(add, t1, t2);
    }

    public static Pair<Term, Term> brkAdd(Term t){
        return t.brkBinary(add);
    }

    // sub
    public static final Const sub = FOL.mkFun(Constants.SUB_Str, int_, int_, int_);

    public static boolean isSub(Term t){
        return t.isBinary(sub);
    }

    public static App mkSub(Term t1, Term t2){
        return Term.mkBinary(sub, t1, t2);
    }

    public static Pair<Term, Term> brkSub(Term t){
        return t.brkBinary(sub);
    }

    // mul
    public static final Const mul = FOL.mkFun(Constants.MUL_Str, int_, int_, int_);

    public static boolean isMul(Term t){
        return t.isBinary(mul);
    }

    public static App mkMul(Term t1, Term t2){
        return Term.mkBinary(mul, t1, t2);
    }

    public static Pair<Term, Term> brkMul(Term t){
        return t.brkBinary(mul);
    }

    // div
    public static final Const div = FOL.mkFun(Constants.DIV_Str, int_, int_, int_);

    public static boolean isDiv(Term t){
        return t.isBinary(div);
    }

    public static App mkDiv(Term t1, Term t2){
        return Term.mkBinary(div, t1, t2);
    }

    public static Pair<Term, Term> brkDiv(Term t){
        return t.brkBinary(div);
    }

    // mod
    public static final Const mod = FOL.mkFun(Constants.MOD_Str, int_, int_, int_);

    public static boolean isMod(Term t){
        return t.isBinary(mod);
    }

    public static App mkMod(Term t1, Term t2){
        return Term.mkBinary(mod, t1, t2);
    }

    public static Pair<Term, Term> brkMod(Term t){
        return t.brkBinary(mod);
    }

    // less
    public static final Const less = FOL.mkFun(Constants.LESS_Str, int_, int_, FOL.bool);

    public static boolean isLess(Term t){
        return t.isBinary(less);
    }

    public static App mkLess(Term t1, Term t2){
        return Term.mkBinary(less, t1, t2);
    }

    public static Pair<Term, Term> brkLess(Term t){
        return t.brkBinary(less);
    }

    // greater
    public static final Const greater = FOL.mkFun(Constants.GREATER_Str, int_, int_, FOL.bool);

    public static boolean isGreater(Term t){
        return t.isBinary(greater);
    }

    public static App mkGreater(Term t1, Term t2){
        return Term.mkBinary(greater, t1, t2);
    }

    public static Pair<Term, Term> brkGreater(Term t){
        return t.brkBinary(greater);
    }

    // lessEq
    public static final Const lessEq = FOL.mkFun(Constants.LESS_OR_EQ_Str, int_, int_, FOL.bool);

    public static boolean isLessEq(Term t){
        return t.isBinary(lessEq);
    }

    public static App mkLessEq(Term t1, Term t2){
        return Term.mkBinary(lessEq, t1, t2);
    }

    public static Pair<Term, Term> brkLessEq(Term t){
        return t.brkBinary(lessEq);
    }

    // greaterEq
    public static final Const greaterEq = FOL.mkFun(Constants.GREATER_OR_EQ_Str, int_, int_, FOL.bool);

    public static boolean isGreaterEq(Term t){
        return t.isBinary(greaterEq);
    }

    public static App mkGreaterEq(Term t1, Term t2){
        return Term.mkBinary(greaterEq, t1, t2);
    }

    public static Pair<Term, Term> brkGreaterEq(Term t){
        return t.brkBinary(greaterEq);
    }
}