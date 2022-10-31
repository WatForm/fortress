package fortress.inputs;

import fortress.problemstate.*;
import fortress.util.Errors;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import fortress.msfol.*;
import scala.util.Either;
import scala.util.Left;

import java.io.*;
import java.util.HashMap;
import java.util.Map;

public class TptpFofParser implements TheoryParser {
    
    @Override
    public Either<Errors.ParserError, Theory> parse(InputStream inputStream) throws IOException {
        CharStream stream = CharStreams.fromStream(inputStream);
        FOFTPTPLexer lexer = new FOFTPTPLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        if (parser.getNumberOfSyntaxErrors() >= 1)
            return new Left<>(new Errors.ParserError("Syntax error"));
        TptpToFortress converter = new TptpToFortress();
        converter.visit(tree);
        return converter.getTheory();
    }

    @Override
    public Either<Errors.ParserError, Theory> parse(String filePath) throws IOException {
        InputStream inputStream = new FileInputStream(filePath);
        CharStream stream = CharStreams.fromStream(inputStream);
        FOFTPTPLexer lexer = new FOFTPTPLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        FOFTPTPParser parser = new FOFTPTPParser(tokens);
        ParseTree tree = parser.spec();
        if (parser.getNumberOfSyntaxErrors() >= 1)
            return new Left<>(new Errors.ParserError("Syntax error"));
        TptpToFortress converter = new TptpToFortress(filePath);
        converter.visit(tree);
        return converter.getTheory();
    }

    @Override
    public Map<Sort, Scope> getScopes(){
        return new HashMap();
    }
}
