package fortress.solverinterface;

import fortress.inputs.*;
import fortress.interpretation.Interpretation;
import fortress.msfol.*;
import fortress.util.Errors;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import scala.util.Either;
import scala.util.Right;

import javax.imageio.IIOException;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;
import java.util.Set;

public class SmtModelParser{

    public SmtModelParser() {}

    public static Either<Errors.ParserError, Set<FunctionDefinition>> parse(String str) throws IOException {
        CharStream inputStream = CharStreams.fromString(str);
        SmtLibSubsetLexer lexer = new StopAtFirstErrorSmtLibLexer(inputStream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        SmtLibSubsetParser parser = new SmtLibSubsetParser(tokens);

        // Use the "give up" error handler for parser
        parser.setErrorHandler(new StopAtFirstErrorStrategy());

        ParseTree tree = parser.commands();
        if (parser.getNumberOfSyntaxErrors() >= 1)
            return null;

        SmtModelVisitor visitor = new SmtModelVisitor();
        visitor.visit(tree);
        Set<FunctionDefinition> functionDefinitions = visitor.getFunctionDefinitions();
        return new Right<>(functionDefinitions);
    }

}
