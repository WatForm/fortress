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

package fortress.lambda.visitor;

import fortress.lambda.*;
import fortress.util.STree;

import java.util.List;

/**
 * Created by Amirhossein Vakili.
 */

 // Visitor to construct an STree representation of a term
public class STreeOfTerm implements TermVisitor<STree> {

    private STreeOfTerm(){}

    public static final STreeOfTerm INS = new STreeOfTerm();

    @Override
    public STree visitVar(Var t) {
        return new STree(t.getName());
    }

    @Override
    public STree visitCon(Con t) {
        return new STree(t.getName());
    }

    @Override
    public STree visitApp(App t) {
        List<Term> tl = t.brkApp();
        STree[] temp = new STree[tl.size() - 1];
        for (int i = 1; i != tl.size(); i++)
            temp[i - 1] = tl.get(i).accept(this);
        return new STree(tl.get(0).toString(), temp);
    }

    @Override
    public STree visitAbs(Abs t) {
        return new STree(t.toString());
    }
}
