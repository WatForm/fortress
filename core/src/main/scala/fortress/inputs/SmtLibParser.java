package fortress.inputs;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import fortress.msfol.*;
import java.io.*;
import java.util.Optional;
import java.util.Map;
import java.util.HashMap;

public class SmtLibParser implements TheoryParser {
    
    private Map<String, String> info;
    private Optional<String> logic;
    
    public SmtLibParser() {
        this.info = new HashMap<>();
        this.logic = Optional.empty();
    }
    
    @Override
    public Theory parse(InputStream inputStream) throws IOException {
        CharStream stream = CharStreams.fromStream(inputStream);
        // Use the "give up" lexer
        SmtLibSubsetLexer lexer = new StopAtFirstErrorSmtLibLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        SmtLibSubsetParser parser = new SmtLibSubsetParser(tokens);
        // Use the "give up" error handler for parser
        parser.setErrorHandler(new StopAtFirstErrorStrategy());

        ParseTree tree = parser.commands();
        if (parser.getNumberOfSyntaxErrors() >= 1)
            return null;
        SmtLibVisitor visitor = new SmtLibVisitor();
        visitor.visit(tree);
        Theory resultTheory = visitor.getTheory();
        this.info = visitor.getInfo();
        this.logic = visitor.getLogic();
        return resultTheory;
    }

    @Override
    public Theory parse(String filePath) throws IOException {
        InputStream inputStream = new FileInputStream(filePath);
        return parse(inputStream);
    }
    
    public Map<String, String> getInfo() {
        return info;
    }
    
    public Optional<String> getLogic() {
        return logic;
    }
}
