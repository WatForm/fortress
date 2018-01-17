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

//import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class PartialFiniteFunction<K, V>{
    
    private Map<K, V> body;
    
    public PartialFiniteFunction(){
        body = new HashMap<K, V>();
    }
    
    public PartialFiniteFunction(List<Pair<K, V>> fun){
        body = new HashMap<K, V>();
        for(Pair<K, V> p: fun)
            body.put(p.left, p.right);
        
    }
    
    public boolean isInDomain(K key){
        return body.containsKey(key);
    }
    
    public V get(K key){
        return body.get(key);
    }
    
    public V get(K key, V defaultValue){
        return body.getOrDefault(key, defaultValue);
    }

    public Set<K> getDomain(){
        return body.keySet();
    }
    
    public void update(K key, V value){
        body.put(key, value);
    }
    
    @Override
    public String toString(){
        return body.toString();
    }
    
    @Override
    public boolean equals(Object other){
        return body.equals(other);
    }
    
    @Override
    public int hashCode(){
        return body.hashCode();
    }    

}
