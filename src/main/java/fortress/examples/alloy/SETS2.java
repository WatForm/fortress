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

package fortress.examples.alloy;

import fortress.fol.FOL;
import fortress.fol.finite_scope_solver.UIFSolver;
import fortress.fol.pterm.PTerm;
import fortress.theory.Theory;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by avakili on 28/05/16.
 */
public final class SETS2 {

    private static void createModel(){
        Theory result = new Theory("SETS2", Theory.ARITH_THEORY);
        PTerm Element = FOL.mkSort("Element");
        PTerm Set = FOL.mkSort("Set");
        result.addCon(FOL.mkFun("elements", Set, Element, FOL.bool));
        result.addAxiom("exists[s: Set. forall[e: Element. !elements[s, e]]]");
        result.addAxiom("forall[s: Set, e: Element. exists[s1: Set. forall[e1: Element. elements[s1, e1] <=> e = e1 | elements[s, e1]]]]");
        result.addAxiom("!forall[s0:Set, s1: Set. exists[s2: Set. forall[e: Element. elements[s2, e] <=> elements[s0, e] | elements[s1, e]]]]");
        UIFSolver solver = new UIFSolver(result);
        Map<PTerm, Integer> bounds = new HashMap<>();
        bounds.put(Element, 5);
        bounds.put(Set, 32);
        solver.verbosity = 1;
        solver.setUniverseByBounds(bounds);
        solver.checkSat(true, false);
        //return result;
    }

    public static void main(String[] args) {
        createModel();
    }
}
