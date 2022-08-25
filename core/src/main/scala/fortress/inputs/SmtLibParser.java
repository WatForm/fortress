package fortress.inputs;

import fortress.util.Errors;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import fortress.msfol.*;
import scala.util.Either;
import scala.util.Right;

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
    public Either<Errors.ParserError, Theory> parse(InputStream inputStream) throws IOException {
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
        return new Right<>(resultTheory);
    }

    @Override
    public Either<Errors.ParserError, Theory> parse(String filePath) throws IOException {
        InputStream inputStream = new FileInputStream(filePath);
        return parse(inputStream);
    }
    
    public Map<String, String> getInfo() {
        return info;
    }
    
    public Optional<String> getLogic() {
        return logic;
    }

    @Override
    public Map<Sort, Scope> getScopes() {
        Map<Sort, Scope> scopes = new HashMap();
        String scopeInfo = this.info.getOrDefault("exact-scope", "");
        // We expect scopeInfo to be in the form "(A 5)(B 3) ..."
        String[] exactScopes = scopeInfo.split("\)");
        // exact scopes now has "(<sort> <scope>" in each index
        for(int i = 0; i < exactScopes.length; i++){
            String info = exactScopes[i];
            int spaceIndex = info.lastIndexOf(' ');
            String sortName = info.substring(1, spaceIndex);
            String scopeSizeString = info.substring(spaceIndex + 1);
            int scopeSize = Integer.parseInt(scopeSizeString);

            Sort sort = new SortConst(sortName);
            ExactScope scope = new ExactScope(scopeSize);
            scopes.put(sort, scope);
        }

        scopeInfo = this.info.getOrDefault("nonexact-scope", "");
        // We expect scopeInfo to be in the form "(A 5)(B 3) ..."
        String[] nonExactScopes = scopeInfo.split("\)");
        // exact scopes now has "(<sort> <scope>" in each index
        for(int i = 0; i < nonExactScopes.length; i++){
            String info = nonExactScopes[i];
            int spaceIndex = info.lastIndexOf(' ');
            String sortName = info.substring(1, spaceIndex);
            String scopeSizeString = info.substring(spaceIndex + 1);
            int scopeSize = Integer.parseInt(scopeSizeString);

            Sort sort = new SortConst(sortName);
            NonExactScope scope = new NonExactScope(scopeSize);
            scopes.put(sort, scope);
        }

        return scopes;
    }
}
