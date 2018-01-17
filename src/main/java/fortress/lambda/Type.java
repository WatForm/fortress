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

/**
 * Created by amirhossein on 13/01/16.
 */

import fortress.Constants;
import fortress.fol.pterm.Com;
import fortress.fol.pterm.PTerm;
import fortress.fol.pterm.PVar;
import fortress.util.Pair;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static fortress.util.Errors.failIf;
import static fortress.util.ListOps.foldLeft;

public final class Type{

    public static Com BOOL = mkSort(Constants.BOOL_Str);

    public static PVar _a = mkVar("_a");

    public static PVar _b = mkVar("_b");

    public static PVar _c = mkVar("_c");

    private Type() {}

    public static PVar mkVar(String name){
        return new PVar(name);
    }

    public static Com mkCom(String functor, PTerm... args){
        //System.out.println(functor + Arrays.asList(args).size());
        return new Com(functor, Arrays.asList(args));
    }

    public static Com mkSort(String name){
        return mkCom(name);
    }

    public static Com mkFnTy(PTerm... args){
        failIf(args.length < 2);
        PTerm result = args[args.length - 1];
        for(int i = args.length - 2; i != -1; --i){
            result = new Com(Constants.FN_Str, new ArrayList<>(Arrays.asList(args[i], result)));
        }
        return (Com) result;
    }

    public static boolean isFnTy(PTerm t){
        return t.isCom() && ((Com) t).getFunctor().equals(Constants.FN_Str);
    }

    public static Pair<PTerm, PTerm> brkFnTy(PTerm t){
        failIf(!isFnTy(t));
        return new Pair<>(((Com) t).getArgs().get(0), ((Com) t).getArgs().get(1));
    }

    public static Pair<List<PTerm>, PTerm> brkFnTys(PTerm t){
        List<PTerm> inputType = new ArrayList<>();
        PTerm temp = t;
        while (temp.isCom() && ((Com) temp).getFunctor().equals(Constants.FN_Str)){
            inputType.add(((Com) temp).getArgs().get(0));
            temp = ((Com) temp).getArgs().get(1);
        }
        return new Pair<>(inputType, temp);
    }

    public static boolean isOutputType(Term t, PTerm ty){
        if (t.ty.equals(ty))
            return true;
        Pair<List<PTerm>, PTerm> p = brkFnTys(t.ty);
        return p.right.equals(ty);
    }

    public static int order(PTerm t){
        if (t.isPVar())
            return 0;
        Com ct = (Com) t;
        if (ct.getFunctor().equals(Constants.FN_Str))
            return Math.max(order(ct.getArgs().get(0)) + 1, order(ct.getArgs().get(1)));
        return foldLeft((n) -> (pt) -> Math.max(n, order(pt)) , 0, ct.getArgs());
    }
}