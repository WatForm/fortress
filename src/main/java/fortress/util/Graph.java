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

import java.util.*;

/**
 * Created by Amirhossein Vakili.
 */
public class  Graph<V, E extends Comparable<? super E>> {

    private List<V> vertex;
    private Set<List<E>>[][]edge;

    public Graph(List<V> vertex){
        this.vertex = vertex;
        final int len = vertex.size();
        edge = new Set[len][len];
        Comparator<List<E>> comp = (l1, l2) -> {
            Iterator<E> it1 = l1.iterator();
            Iterator<E> it2 = l2.iterator();
            while (it1.hasNext() && it2.hasNext()){
                int test = it1.next().compareTo(it2.next());
                if (test != 0)
                    return test;
            }
            if (it1.hasNext())
                return 1;
            if (it2.hasNext())
                return -1;
            return 0;
        };
        for (int i = 0; i != len; i++)
            for (int j = 0; j!= len; j++)
                edge[i][j] = new TreeSet<>(comp);
    }

    public void addEdge(V v1, V v2, E e){
        List<E> temp = new LinkedList<>();
        temp.add(e);
        edge[vertex.indexOf(v1)][vertex.indexOf(v2)].add(temp);
    }

    public void uniquePaths(){
        final int len = vertex.size();
        for (int count = 1; count < len; count *= 2){
            for (int i = 0; i != len; i++)
                for (int j = 0; j != len; j++){
                    for (int k = 0; k != len; k++) {
                        if (k == i || k == j)
                            continue;
                        for (List<E> pik: edge[i][k])
                            for (List<E> pkj: edge[k][j]){
                                List<E> temp = new LinkedList<>();
                                temp.addAll(pik);
                                temp.addAll(pkj);
                                edge[i][j].add(temp);
                            }
                    }
                }
        }
    }

    public List<E> shortestPath(V v1, V v2){
        Iterator<List<E>> it = edge[vertex.indexOf(v1)][vertex.indexOf(v2)].iterator();
        if (!it.hasNext())
            return null;
        List<E> result = it.next();
        while (it.hasNext()) {
            List<E> p = it.next();
            if (p.size() < result.size())
                result = p;
        }
        return result;
    }

    public boolean isOnCycle(E e){
        for (int i = 0; i != vertex.size(); i++)
            for (List<E> p: edge[i][i])
                if (p.contains(e))
                    return true;
        return false;
    }
}
