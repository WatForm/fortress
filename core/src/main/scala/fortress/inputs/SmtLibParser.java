package fortress.inputs;

import fortress.problemstate.*;
import fortress.util.Errors;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import fortress.msfol.*;
import scala.util.Either;
import scala.util.Right;

import java.io.*;
import java.util.Optional;
import java.util.Map;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.MatchResult;
import java.util.regex.Pattern;

public class SmtLibParser implements TheoryParser {
    
    private Map<String, String> info;
    private Optional<String> logic;

    private boolean usingSmtPlus;

    protected final Pattern scopesPattern = Pattern.compile("(\\(\\s*(?<sort>[[a-zA-Z][~!@$%^&*_\\-+=<>.?/]][[a-zA-Z][~!@$%^&*_\\-+=<>.?/][0-9]]*|\\|[[\\u0021-\\u005B][\\u005D-\\u007B][\\u007D-\\u007E]\\s]+\\|)\\s+(?<scope>[0-9]+)\\s*\\))");
    protected final Pattern fixedPattern = Pattern.compile("(\\(\\s*(?<sort>[[a-zA-Z][~!@$%^&*_\\-+=<>.?/]][[a-zA-Z][~!@$%^&*_\\-+=<>.?/][0-9]]*|\\|[[\\u0021-\\u005B][\\u005D-\\u007B][\\u007D-\\u007E]\\s]+\\|)\\s*\\))");
    
    public SmtLibParser(boolean usingSmtPlus) {
        this.info = new HashMap<>();
        this.logic = Optional.empty();
        this.usingSmtPlus = usingSmtPlus;
    }

    public SmtLibParser(){
        this(false);
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
        SmtLibVisitor visitor = new SmtLibVisitor(usingSmtPlus);
        visitor.visit(tree);
        Theory resultTheory = visitor.getTheory();
        this.info = visitor.getInfo();
        this.logic = visitor.getLogic();
        return new Right<>(resultTheory);
    }

    @Override
    public Either<Errors.ParserError, Theory> parse(String filePath) throws IOException {
        InputStream inputStream = new FileInputStream(filePath);

        if (filePath.endsWith(".smt+") || filePath.endsWith(".smttc")){
            usingSmtPlus = true;
        } else {
            usingSmtPlus = false;
        }

        return parse(inputStream);
    }
    
    public Map<String, String> getInfo() {
        return info;
    }
    
    public Optional<String> getLogic() {
        return logic;
    }

    protected String withoutBarQuotes(String input){
        if (input.charAt(0) == '|'){
            return input.substring(1, input.length() -1);
        } else {
            return input;
        }
    }

    protected Sort sortFromName(String name){
        name = withoutBarQuotes(name);
        if (name.equals("Int") || name.equals("IntSort")){
            return IntSort$.MODULE$;
        } else {
            return new SortConst(name);
        }
    }

    @Override
    public Map<Sort, Scope> getScopes() throws IOException {
        Map<Sort, Scope> scopes = new HashMap<Sort, Scope>();

        
        HashSet<Sort> unchangingSorts = new HashSet<Sort>();

        String unchangingSortInfo = info.getOrDefault("unchanging-scope", "");
        if (!unchangingSortInfo.isEmpty()){
            // Split at closing parens
            // Start matching the data
            Matcher unchangingMatcher = fixedPattern.matcher(unchangingSortInfo);
            int previousEnd = -1;
            System.out.println(unchangingSortInfo);
            while(unchangingMatcher.find()){
                // Ensure only whitespace between
                for (int i = previousEnd+1; i < unchangingMatcher.start(); i++){
                    if (!Character.isWhitespace(unchangingSortInfo.charAt(i))){
                        throw new IOException("Malformed unchanging-scope info at character " + i + ".");
                    }
                }
                previousEnd = unchangingMatcher.end();
                // Extract the sort
                String sortName = unchangingMatcher.group("sort");
                sortName = withoutBarQuotes(sortName);
                Sort sort = sortFromName(sortName);
                unchangingSorts.add(sort);
            }
        }
        
        


        String scopeInfo = this.info.getOrDefault("exact-scope", "");
        // We expect scopeInfo to be in the form "(A 5)(B 3) ..."

        if (!scopeInfo.isEmpty()){
            Matcher scopesMatcher = scopesPattern.matcher(scopeInfo);

            int previousEnd = -1;
            while(scopesMatcher.find()){
                // Ensure only whitespace between
                for (int i = previousEnd+1; i < scopesMatcher.start(); i++){
                    if (!Character.isWhitespace(scopeInfo.charAt(i))){
                        throw new IOException("Malformed exact-scope info at character " + i + ".");
                    }
                }
                previousEnd = scopesMatcher.end();

                String sortName = scopesMatcher.group("sort");
                Sort sort = sortFromName(sortName);
                
                int scopeSize = Integer.parseInt(scopesMatcher.group("scope"));

                ExactScope scope = new ExactScope(scopeSize, unchangingSorts.contains(sort));
                
                scopes.put(sort, scope);
            }
        }
        

        scopeInfo = this.info.getOrDefault("nonexact-scope", "");
        if (!scopeInfo.isEmpty()){
            Matcher scopesMatcher = scopesPattern.matcher(scopeInfo);

            int previousEnd = -1;
            while(scopesMatcher.find()){
                // Ensure only whitespace between
                for (int i = previousEnd+1; i < scopesMatcher.start(); i++){
                    if (!Character.isWhitespace(scopeInfo.charAt(i))){
                        throw new IOException("Malformed nonexact-scope info at character " + i + ".");
                    }
                }
                previousEnd = scopesMatcher.end();

                String sortName = scopesMatcher.group("sort");
                Sort sort = sortFromName(sortName);
                
                int scopeSize = Integer.parseInt(scopesMatcher.group("scope"));

                NonExactScope scope = new NonExactScope(scopeSize, unchangingSorts.contains(sort));
                
                scopes.put(sort, scope);
            }
        }

        return scopes;
    }
}
