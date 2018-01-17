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

package fortress;

import fortress.formats.tptp.FOF2Alloy;
import fortress.formats.tptp.FOFTPTPLexer;
import fortress.formats.tptp.FOFTPTPParser;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;

import java.io.FileInputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

public class Main {

    private static void run(String name){
        ANTLRInputStream input = null;
        try {
            input = new ANTLRInputStream(new FileInputStream(name + ".p"));
        } catch (IOException e){
            e.printStackTrace();
            return;
        }
        FOFTPTPLexer lexer = new FOFTPTPLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        FOF2Alloy trans = new FOF2Alloy();
        System.out.println(trans.visit(tree));

    }
    
    public static void main(String[] args) throws Exception {
        if (args.length == 1)
            run(args[0]);
        //else
        //    run("/home/amirhossein/Dropbox/fortress/tptp/fof/infinity");
    }

}
