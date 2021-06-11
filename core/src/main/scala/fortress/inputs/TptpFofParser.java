package fortress.inputs;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import fortress.msfol.*;
import java.io.*;

public class TptpFofParser implements TheoryParser {
    
    @Override
    public Theory parse(InputStream inputStream) throws IOException {
        CharStream stream = CharStreams.fromStream(inputStream);
        FOFTPTPLexer lexer = new FOFTPTPLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        TptpToFortress converter = new TptpToFortress();
        converter.visit(tree);
        return converter.getTheory();
    }

    @Override
    public Theory parse(String filePath) throws IOException {
        InputStream inputStream = new FileInputStream(filePath);
        CharStream stream = CharStreams.fromStream(inputStream);
        FOFTPTPLexer lexer = new FOFTPTPLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        TptpToFortress converter = new TptpToFortress(filePath);
        converter.visit(tree);
        return converter.getTheory();
    }
}
