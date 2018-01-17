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

package fortress.examples.tptp.fof;

import fortress.fol.finite_scope_solver.UIFSolver;
import fortress.fol.pterm.PTerm;
import fortress.formats.tptp.FOF2Fortress;
import fortress.formats.tptp.FOFTPTPLexer;
import fortress.formats.tptp.FOFTPTPParser;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

/**
 * Created by Amirhossein Vakili.
 */
public final class CaseStudies {

    private static void run(String name, int size){
        System.out.println("***************");
        System.out.println("*****BEGIN*****");
        System.out.println("***************");
        System.out.println("solving " + name + " for " + size);
        ANTLRInputStream input = null;
        try {
            input = new ANTLRInputStream(new FileInputStream(name + ".p"));
        } catch (IOException e) {
            e.printStackTrace();
        }
        FOFTPTPLexer lexer = new FOFTPTPLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        FOF2Fortress trans = new FOF2Fortress(name);
        trans.visit(tree);
        UIFSolver solver = new UIFSolver(trans.result);
        Map<PTerm, Integer> bounds = new HashMap<>();
        bounds.put(trans.univ, size);
        //System.out.println(trans.result);
        solver.verbosity = 1;
        solver.setUniverseByBounds(bounds);
        solver.checkSat(true, false);
        System.out.println("***************");
        System.out.println("******END******");
        System.out.println("***************");

    }

    private static void generate(String name, int size){
        System.out.println("Generating " + name + " for " + size);
        ANTLRInputStream input = null;
        try {
            input = new ANTLRInputStream(new FileInputStream(name + ".p"));
        } catch (IOException e) {
            e.printStackTrace();
        }
        FOFTPTPLexer lexer = new FOFTPTPLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        FOF2Fortress trans = new FOF2Fortress(name);
        trans.visit(tree);
        UIFSolver solver = new UIFSolver(trans.result);
        Map<PTerm, Integer> bounds = new HashMap<>();
        bounds.put(trans.univ, size);
        //System.out.println(trans.result);
        solver.verbosity = 1;
        solver.setUniverseByBounds(bounds);
        solver.generate(true, false, name, size);
        System.out.println("***************");
        System.out.println("******END******");
        System.out.println("***************");
    }

    public static void main(String[] args) {
        if (args.length == 2)
            run(args[0], Integer.parseInt(args[1]));
        if (args.length == 3)
            generate(args[0], Integer.parseInt(args[1]));
        if (args.length == 1)
            run("med-fm16", Integer.parseInt(args[0])); //0.7
        //run("infinity", 20);
        //run("alg195", 14);
        //run("alg197", 14);
        //run("alg212", 8);
        //run("com008", 9);
        //run("geo091", 10);
        //run("geo158", 10);

        //run("med009", 10);
        //run("num374", 5);
        //run("num378", 21);
        //run("set943", 7);
        //run("set948", 7);
        //run("top020", 9);
    }
}
