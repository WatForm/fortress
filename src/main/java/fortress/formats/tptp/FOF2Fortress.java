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

package fortress.formats.tptp;

import fortress.fol.FOL;
import fortress.fol.pterm.PTerm;
import fortress.lambda.Con;
import fortress.lambda.Term;
import fortress.lambda.Var;
import fortress.theory.Theory;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.*;

/**
 * Created by Amirhossein Vakili.
 */

 // Visits a parse tree and constructs a theory
public class FOF2Fortress extends FOFTPTPBaseVisitor {

    public Theory result;

    //private Map<String, Integer> relSym, funSym;

    private Set<String> vars;

    public static final PTerm univ = FOL.mkSort("_UNIV");

    public FOF2Fortress(String name){
        result = new Theory(name, Theory.ARITH_THEORY);
        //relSym = new HashMap<>();
        //funSym = new HashMap<>();
        vars = new TreeSet<>();
    }

    // Add formulas as axioms to theory, or if the formula is a conjecture,
    // add its negation as an axiom
    @Override
    public Object visitFof_annotated(FOFTPTPParser.Fof_annotatedContext ctx) {
        vars.clear();
        Term f = (Term) visit(ctx.fof_formula());
        if (ctx.ID(1).getText().equals("conjecture"))
            result.addAxiom(FOL.mkNot(f));
        else
            result.addAxiom(f);
        return null;
    }

    @Override
    public Object visitNot(FOFTPTPParser.NotContext ctx) {
        return FOL.mkNot((Term) visit(ctx.fof_formula()));
    }

    @Override
    public Object visitForall(FOFTPTPParser.ForallContext ctx){
        List<Var> vars1 = new LinkedList<>();
        for (TerminalNode n: ctx.ID()) {
            String name = n.getText();
            vars.add(name);
            vars1.add(new Var(name, univ));
        }
        return FOL.mkForall(vars1, (Term) visit(ctx.fof_formula()));
    }

    @Override
    public Object visitExists(FOFTPTPParser.ExistsContext ctx){
        List<Var> vars1 = new LinkedList<>();
        for (TerminalNode n: ctx.ID()) {
            String name = n.getText();
            vars.add(name);
            vars1.add(new Var(name, univ));
        }
        return FOL.mkExists(vars1, (Term) visit(ctx.fof_formula()));
    }

    @Override
    public Object visitAnd(FOFTPTPParser.AndContext ctx){
        return FOL.mkAnd((Term) visit(ctx.fof_formula(0)), (Term) visit(ctx.fof_formula(1)));
    }

    @Override
    public Object visitOr(FOFTPTPParser.OrContext ctx){
        return FOL.mkOr((Term) visit(ctx.fof_formula(0)), (Term) visit(ctx.fof_formula(1)));
    }

    @Override
    public Object visitImp(FOFTPTPParser.ImpContext ctx){
        return FOL.mkImp((Term) visit(ctx.fof_formula(0)), (Term) visit(ctx.fof_formula(1)));
    }

    @Override
    public Object visitIff(FOFTPTPParser.IffContext ctx){
        return FOL.mkIff((Term) visit(ctx.fof_formula(0)), (Term) visit(ctx.fof_formula(1)));
    }

    @Override
    public Object visitEq(FOFTPTPParser.EqContext ctx){
        return FOL.mkEq((Term) visit(ctx.term(0)), (Term) visit(ctx.term(1)));
    }

    @Override
    public Object visitNeq(FOFTPTPParser.NeqContext ctx){
        return FOL.mkNot(FOL.mkEq((Term) visit(ctx.term(0)), (Term) visit(ctx.term(1))));
    }

    @Override
    public Object visitProp(FOFTPTPParser.PropContext ctx){
        String temp = ctx.ID().getText();
        //relSym.put(temp, 0);
        return FOL.mkProp(temp);
    }

    @Override
    public Object visitPred(FOFTPTPParser.PredContext ctx){
        String temp = ctx.ID().getText();
        final int len = ctx.term().size();
        //relSym.put(temp, len);
        PTerm [] ty = new PTerm[len + 1];
        List<Term> args = new LinkedList<>();
        for (int i = 0; i != len; i++) {
            ty[i] = univ;
            args.add((Term) visit(ctx.term(i)));
        }
        ty[len] = FOL.bool;
        return FOL.apply(FOL.mkFun(temp, ty), args);
    }

    @Override
    public Object visitParen(FOFTPTPParser.ParenContext ctx){
        return visit(ctx.fof_formula());
    }

    @Override
    public Object visitConVar(FOFTPTPParser.ConVarContext ctx){
        String name = ctx.ID().getText();
        if (vars.contains(name))
            return new Var(name, univ);
        //funSym.put(name, 0);
        return new Con(name, univ);
    }

    @Override
    public Object visitApply(FOFTPTPParser.ApplyContext ctx){
        String name = ctx.ID().getText();
        final int len = ctx.term().size();
        //funSym.put(name, len);
        PTerm [] ty = new PTerm[len + 1];
        List<Term> args = new LinkedList<>();
        for (int i = 0; i != len; i++) {
            ty[i] = univ;
            args.add((Term) visit(ctx.term(i)));
        }
        ty[len] = univ;
        return FOL.apply(FOL.mkFun(name, ty), args);
    }
}
