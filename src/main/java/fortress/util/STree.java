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

/**
 * Created by Amirhossein Vakili.
 */

// Class to create s-trees using string data
public class STree implements Comparable<STree>{

    private String data;

    private STree[] children;

    public STree(String data){
        this.data = data;
    }

    public STree(String data, STree... children){
        this.data = data;
        if (children == null)
            this.children = null;
        else
            this.children = children;
    }

    public STree(String... stree){
        data = stree[0];
        children = new STree[stree.length - 1];
        for (int i = 1; i < stree.length; i++)
            children[i - 1] = new STree(stree[i]);
    }

    public STree(STree st){
        this.data = st.data;
        if (children == null) {
            children = null;
            return;
        }
        children = new STree[st.children.length];
        for (int i = 0; i != st.children.length; i++)
            children[i] = new STree(st.children[i]);
    }

    public boolean isLeaf(){
        return children != null;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append(data.toString());
        if (children == null || children.length == 0)
            return sb.toString();
        sb.append('[');
        sb.append(children[0].toString());
        for (int i = 1; i != children.length; i++ ) {
            sb.append(", ");
            sb.append(children[i].toString());
        }
        sb.append(']');
        return sb.toString();
    }

    @Override
    public boolean equals(Object o){
        if (o == null)
            return false;
        if (o == this)
            return true;
        if (getClass() != o.getClass())
            return false;
        STree other = (STree) o;
        if (!data.equals(other.data))
            return false;
        if (children == other.children)
            return true;
        if (children == null || other.children == null)
            return false;
        if (children.length != other.children.length)
            return false;
        for (int i = 0; i != children.length; i++)
            if (!children[i].equals(other.children[i]))
                return false;
        return true;
    }

    @Override
    public int compareTo(STree other){
        if (this == other)
            return 0;
        int test = data.compareTo(other.data);
        if (test != 0)
            return test;
        for (int i = 0; i != Math.min(children.length, other.children.length); i++){
            test = children[i].compareTo(other.children[i]);
            if (test != 0)
                return test;
        }
        return children.length - other.children.length;
    }

    @Override
    public int hashCode(){
        final int prime = 31;
        int result = data.hashCode();
        if (children == null)
            return result;
        for (STree tree: children)
            result = prime * result + tree.hashCode();
        return result;
    }

    public boolean eq(STree other){
        if (other == this)
            return true;
        if (!data.equals(other.data))
            return false;
        if (children == other.children)
            return true;
        if (children == null || other.children == null)
            return false;
        if (children.length != other.children.length)
            return false;
        for (int i = 0; i != children.length; i++)
            if (!children[i].eq(other.children[i]))
                return false;
        return true;
    }

}
