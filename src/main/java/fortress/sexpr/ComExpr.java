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

package fortress.sexpr;


import java.util.Arrays;
import java.util.List;

import static fortress.util.Errors.failIf;

/**
 * Created by amirhossein on 17/01/16.
 */
public class ComExpr extends SExpr {

    private SExpr[] body;
    private int len;

    public ComExpr(List<SExpr> body){
        failIf(body == null);
        len = Math.max(body.size() - 1, 0) + 2;
        this.body = new SExpr[body.size()];
        int i = 0;
        for (SExpr s: body) {
            failIf(s == null);
            len += s.length();
            this.body[i++] = s;
        }
    }

    public ComExpr(SExpr...body){
        ComExpr temp = new ComExpr(Arrays.asList(body));
        this.body = temp.body;
        this.len = temp.len;
    }

    @Override
    public int length(){
        return len;
    }

    @Override
    public String toString() {
        if (len == 2)
            return "()";
        StringBuilder sb = new StringBuilder(len);
        sb.append('(');
        sb.append(body[0].toString());
        for (int i = 1; i != body.length; i++) {
            sb.append(' ');
            sb.append(body[i].toString());
        }
        sb.append(')');
        return sb.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (o == null)
            return false;
        if (o == this)
            return true;
        if (getClass() != o.getClass())
            return false;
        ComExpr other = (ComExpr) o;
        int minLength = Math.min(body.length, other.body.length);
        for (int i = 0; i != minLength; i++){
            if (!body[i].equals(other.body[i]))
                return false;
        }
        if (minLength != body.length || minLength != other.body.length)
            return false;
        return true;
    }

    @Override
    public int compareTo(SExpr o) {
        failIf(o == null);
        if (o == this)
            return 0;
        if (getClass() != o.getClass())
            return 1;
        ComExpr other = (ComExpr) o;
        int minLength = Math.min(body.length, other.body.length);
        for (int i = 0; i != minLength; i++){
            int test = body[i].compareTo(other.body[i]);
            if (test != 0)
                return test;
        }
        if (minLength != other.body.length)
            return 1;
        if (minLength != body.length)
            return -1;
        return 0;
    }

    @Override
    public int hashCode() {
        final int prime = 37;
        int result = 1;
        for (int i = 0; i != body.length; i++)
            result = prime * result + body[i].hashCode();
        return result;
    }
    
    @Override
    public <T> T accept(SExprVisitor<T> visitor) {
        return visitor.visitComExpr(this);
    }

}
