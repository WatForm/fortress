package fortress.inputs;

import fortress.inputs.*;
import fortress.interpretation.BasicInterpretation;
import fortress.interpretation.Interpretation;
import fortress.msfol.*;
import fortress.util.Errors;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import scala.collection.Seq;
import scala.collection.immutable.HashMap;
import scala.util.Either;
import scala.util.Right;

import javax.imageio.IIOException;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class SmtModelParser{

    public SmtModelParser() {}

    public static SmtModelVisitor parse(String str, Signature signature) throws IOException {

        CharStream inputStream = CharStreams.fromString(str); // get inputStream from input string(model return from smt solver)

        SmtLibSubsetLexer lexer = new StopAtFirstErrorSmtLibLexer(inputStream); // lexer

        CommonTokenStream tokens = new CommonTokenStream(lexer); // tokens

        SmtLibSubsetParser parser = new SmtLibSubsetParser(tokens); // parser

        // Use the "give up" error handler for parser
        parser.setErrorHandler(new StopAtFirstErrorStrategy());

        ParseTree tree = parser.commands(); // get syntax tree

        if (parser.getNumberOfSyntaxErrors() >= 1)
            return null;

        SmtModelVisitor visitor = new SmtModelVisitor(signature);
        visitor.visit(tree);

//        Map<Sort, Seq<Value>> sortInterpretations = visitor.getSortInterpretations();
//        Map<AnnotatedVar, Value> constantInterpretations = visitor.getConstantInterpretations();
//        Set<FunctionDefinition> functionDefinitions = visitor.getFunctionDefinitions();

        return visitor;
    }

}
