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

package fortress.formats;

import java.util.*;

/**
 * Created by Amirhossein Vakili.
 */
public class FOF2Alloy extends FOFTPTPBaseVisitor<String> {

    private Map<String, Integer> relSym, funSym;

    private Set<String> constants, props, sets;

    private Set<String> vars;

    public static final String univ = "_UNIV";

    public FOF2Alloy(){
        relSym = new HashMap<>();
        funSym = new HashMap<>();
        constants = new TreeSet<>();
        props = new TreeSet<>();
        sets = new TreeSet<>();
        vars = new TreeSet<>();
    }

    private String predDec(int n){
        StringBuilder sb = new StringBuilder("set _UNIV");
        for (int i = 0; i < n - 2; i++)
            sb.append(" -> set _UNIV");
        return sb.toString();
    }

    private String funDec(int n){
        if (n == 1)
            return "one _UNIV";
        StringBuilder sb = new StringBuilder("set _UNIV");
        for (int i = 0; i < n - 2; i++)
            sb.append(" -> set _UNIV");
        sb.append(" -> one _UNIV");
        return sb.toString();
    }

    @Override
    public String visitSpec(FOFTPTPParser.SpecContext ctx){
        StringBuilder facts = new StringBuilder("fact{\n");
        for (FOFTPTPParser.Fof_annotatedContext n: ctx.fof_annotated())
            facts.append("    " + visit(n) + "\n\n");
        facts.append("}\n");
        StringBuilder declarations = new StringBuilder("sig _UNIV{\n");
        if (!relSym.isEmpty()) {
            Iterator<Map.Entry<String, Integer>> it = relSym.entrySet().iterator();
            Map.Entry<String, Integer> el = it.next();
            declarations.append("    " + el.getKey() + " : " + predDec(el.getValue()));
            while (it.hasNext()){
                el = it.next();
                declarations.append(",\n    " + el.getKey() + " : " + predDec(el.getValue()));
            }
            for (Map.Entry<String, Integer> e: funSym.entrySet()){
                declarations.append(",\n    " + e.getKey() + " : " + funDec(e.getValue()));
            }
        } else{
            if (!funSym.isEmpty()){
                Iterator<Map.Entry<String, Integer>> it = funSym.entrySet().iterator();
                Map.Entry<String, Integer> el = it.next();
                declarations.append("    " + el.getKey() + " : " + funDec(el.getValue()));
                while (it.hasNext()){
                    el = it.next();
                    declarations.append(",\n    " + el.getKey() + " : " + funDec(el.getValue()));
                }
            }
        }
        declarations.append("\n}\n");

        if (!constants.isEmpty()){
            declarations.append("one sig ");
            Iterator<String> it = constants.iterator();
            declarations.append(it.next());
            while (it.hasNext())
                declarations.append(", " + it.next());
            declarations.append(" in _UNIV{}\n\n");
        }

        if (!sets.isEmpty()){
            declarations.append("sig ");
            Iterator<String> it = sets.iterator();
            declarations.append(it.next());
            while (it.hasNext())
                declarations.append(", " + it.next());
            declarations.append(" in _UNIV{}\n");
        }
        declarations.append('\n');
        if (!props.isEmpty()){
            declarations.append("one sig _BOOLEAN{}\nsig ");
            Iterator<String> it = props.iterator();
            declarations.append(it.next());
            while (it.hasNext())
                declarations.append(", " + it.next());
            declarations.append(" in _BOOLEAN{}\n\n");
        }
        return declarations.toString() + facts.toString();
    }

    @Override
    public String visitFof_annotated(FOFTPTPParser.Fof_annotatedContext ctx) {
        vars.clear();
        String f = visit(ctx.fof_formula());
        if (ctx.ID(1).getText().equals("conjecture"))
            return "(not " + f + ")";
        return f;
    }

    @Override
    public String visitNot(FOFTPTPParser.NotContext ctx) {
        return  "(not " + visit(ctx.fof_formula()) + ")";
    }

    @Override
    public String visitForall(FOFTPTPParser.ForallContext ctx){
        StringBuilder sb = new StringBuilder("(all ");
        sb.append(ctx.ID(0).getText() + "_");
        vars.add(ctx.ID(0).getText() + "_");
        final int len = ctx.ID().size();
        for (int i = 1; i != len; i++) {
            String name = ctx.ID(i).getText() + "_";
            vars.add(name);
            sb.append(", " + name);
        }
        sb.append(": " + univ + " | " + visit(ctx.fof_formula()) + ")");
        return sb.toString();
    }

    @Override
    public String visitExists(FOFTPTPParser.ExistsContext ctx){
        StringBuilder sb = new StringBuilder("(some ");
        sb.append(ctx.ID(0).getText() + "_");
        vars.add(ctx.ID(0).getText() + "_");
        final int len = ctx.ID().size();
        for (int i = 1; i != len; i++) {
            String name = ctx.ID(i).getText() + "_";
            vars.add(name);
            sb.append(", " + name);
        }
        sb.append(": " + univ + " | " + visit(ctx.fof_formula()) + ")");
        return sb.toString();
    }

    @Override
    public String visitAnd(FOFTPTPParser.AndContext ctx){
        return "(" + visit(ctx.fof_formula(0)) + " and " + visit(ctx.fof_formula(1)) + ")";
    }

    @Override
    public String visitOr(FOFTPTPParser.OrContext ctx){
        return "(" + visit(ctx.fof_formula(0)) + " or " + visit(ctx.fof_formula(1)) + ")";
    }

    @Override
    public String visitImp(FOFTPTPParser.ImpContext ctx){
        return "(" + visit(ctx.fof_formula(0)) + " implies " + visit(ctx.fof_formula(1)) + ")";
    }

    @Override
    public String visitIff(FOFTPTPParser.IffContext ctx){
        return "(" + visit(ctx.fof_formula(0)) + " iff " + visit(ctx.fof_formula(1)) + ")";
    }

    @Override
    public String visitEq(FOFTPTPParser.EqContext ctx){
        return "(" + visit(ctx.term(0)) + " = " + visit(ctx.term(1)) + ")";
    }

    @Override
    public String visitNeq(FOFTPTPParser.NeqContext ctx){
        return "(not (" + visit(ctx.term(0)) + " = " + visit(ctx.term(1)) + "))";
    }

    @Override
    public String visitProp(FOFTPTPParser.PropContext ctx){
        String temp = ctx.ID().getText() + "_";
        props.add(temp);
        return "(some " + temp + ")";
    }

    @Override
    public String visitPred(FOFTPTPParser.PredContext ctx){
        String name = ctx.ID().getText() + "_";
        final int len = ctx.term().size();
        if (len == 1)
            sets.add(name);
        else
            relSym.put(name, len);
        StringBuilder sb = new StringBuilder("((");
        sb.append(visit(ctx.term(0)));
        for (int i = 1; i != len; i++) {
            sb.append(' ');
            sb.append('-');
            sb.append('>');
            sb.append(' ');
            sb.append(visit(ctx.term(i)));
        }
        sb.append(") in " + name + ")");
        return sb.toString();
    }

    @Override
    public String visitParen(FOFTPTPParser.ParenContext ctx){
        return "(" + visit(ctx.fof_formula()) + ")";
    }

    @Override
    public String visitConVar(FOFTPTPParser.ConVarContext ctx){
        String name = ctx.ID().getText() + "_";
        if (!vars.contains(name)) {
            constants.add(name);
            //System.out.println("Adding " + name);
        }
        return name;
    }

    @Override
    public String visitApply(FOFTPTPParser.ApplyContext ctx){
        String name = ctx.ID().getText() + "_";
        final int len = ctx.term().size();
        funSym.put(name, len);
        StringBuilder sb = new StringBuilder(name);
        sb.append('[');
        sb.append(visit(ctx.term(0)));
        for (int i = 1; i != len; i++) {
            sb.append(' ');
            sb.append(',');
            sb.append(visit(ctx.term(i)));
        }
        sb.append(']');
        return sb.toString();
    }
}
