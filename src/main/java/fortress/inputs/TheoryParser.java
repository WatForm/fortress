package fortress.inputs;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import fortress.tfol.*;
import java.io.*;

public class TheoryParser {
    
    public static class TptpFofResult {
        public Theory theory;
        public Type universeType;
        
        public TptpFofResult(Theory theory, Type universeType) {
            this.theory = theory;
            this.universeType = universeType;
        }
    }
    
    public static TptpFofResult parseTptpFof(InputStream inputStream) throws IOException {
        CharStream stream = CharStreams.fromStream(inputStream);
        FOFTPTPLexer lexer = new FOFTPTPLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        TptpToFortress converter = new TptpToFortress();
        converter.visit(tree);
        Theory resultTheory = converter.getTheory();
        Type universeType = converter.getUniverseType();
        return new TptpFofResult(resultTheory, universeType);
    }
    
    public static Theory parseSmtLib(InputStream inputStream) throws IOException {
        CharStream stream = CharStreams.fromStream(inputStream);
        SmtLibSubsetLexer lexer = new SmtLibSubsetLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        SmtLibSubsetParser parser = new SmtLibSubsetParser(tokens);
        ParseTree tree = parser.commands();
        SmtLibToTheory converter = new SmtLibToTheory();
        converter.visit(tree);
        Theory resultTheory = converter.getTheory();
        return resultTheory;
    }
}
