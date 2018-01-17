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

package fortress.fol.pterm.visitor;

import fortress.fol.pterm.Com;
import fortress.fol.pterm.PTerm;
import fortress.fol.pterm.PVar;

/**
 * Created by Amirhossein Vakili.
 */
public class MaxIDPTerm implements PTermVisitor<Integer> {

    private String id;

    public MaxIDPTerm(String id){
        this.id = id;
    }

    @Override
    public Integer visitPVar(PVar t) {
        if (t.getName().matches(id + "[0-9]*")){
            String n = t.getName().substring(id.length());
            if (!n.isEmpty())
                return Integer.parseInt(n) + 1;
        }
        return 0;
    }

    @Override
    public Integer visitCom(Com t) {
        int result = 0;
        if (t.getFunctor().matches(id + "[0-9]*")){
            String n = t.getFunctor().substring(id.length());
            if (!n.isEmpty())
                result = Integer.parseInt(n) + 1;
        }
        for(PTerm pt: t.getArgs())
            result = Math.max(result, pt.accept(this));
        return result;
    }
}
