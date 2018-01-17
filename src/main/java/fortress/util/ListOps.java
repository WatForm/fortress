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

package fortress.util;

import java.util.List;
import java.util.function.Function;
import java.util.function.Predicate;

import static fortress.util.Errors.failIf;

public final class ListOps {
    
    private ListOps(){}
    
    public static <T> T hd(List<T> l){
        failIf(l.size() == 0);
        return l.get(0);
    }
    
    public static <T> List<T> tl(List<T> l){
        failIf(l.size() == 0);
        return l.subList(1, l.size());
    }

    public static <T> boolean forall(Predicate<? super T> pred, List<T> l){
        for(T t: l)
            if(! pred.test(t)) return false;
        return true;
    }
    
    public static <T> boolean exists(Predicate<? super T> pred, List<T> l){
        for(T t: l)
            if(pred.test(t))
                return true;
        return false;
    }
    
    public static <A, B> A foldLeft(Function<? super A, Function<? super B, ? extends A>> f, A a, List<B> l){
        A result = a;
        for(B b: l)
            result = f.apply(result).apply(b);        
        return result;
        
    }

    public static <A, B> B foldRight(Function<? super A, Function<? super B, ? extends B>> f, List<A> l, B b){
        B result = b;
        for(int i = l.size() - 1 ; i != -1; --i)
            result = f.apply(l.get(i)).apply(result);       
        return result;
        
    }
    
    public static <T extends Comparable<? super T>> int compareList(List<T> l1, List<T> l2){
        int minSize = l1.size() <= l2.size() ? l1.size() : l2.size();        
        for(int i = 0; i != minSize; i++)
            if (l1.get(i).compareTo(l2.get(i)) != 0)
                return l1.get(i).compareTo(l2.get(i));        
        return l1.size() - l2.size();
    }

    public static <T> void addIf(List<T> l1, List<T> l2, T e, boolean condition){
        if (condition)
            l1.add(e);
        else l2.add(e);
    }
    
}
