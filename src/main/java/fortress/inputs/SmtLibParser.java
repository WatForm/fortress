package fortress.inputs;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import fortress.tfol.*;
import java.io.*;

public class SmtLibParser implements TheoryParser {
    
    @Override
    public Theory parse(InputStream inputStream) throws IOException {
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
