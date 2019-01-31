package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import fortress.formats.smt.smtlib.*;
import java.util.stream.Collectors;
import java.io.*;
import fortress.util.Errors;

public class Z3CommandLine implements SolverStrategy {
    public Z3CommandLine() {
        // Empty
    }
    
    public ModelFinder.Result solve(Theory theory, int timeout) {
        // TODO need more robust error handling
        try {
            File tempOutputFile = File.createTempFile("fortress", ".smt");
            BufferedWriter writer = new BufferedWriter(new FileWriter(tempOutputFile));
            writeSmtLib(theory, writer);
            writer.flush();
            writer.close();
        
            String command = "z3 -smt2 -memory:2500 -T:2000 ";
            Process process = Runtime.getRuntime().exec(command + tempOutputFile.getAbsolutePath());
            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            Errors.failIf(null == reader);
            String firstLine = reader.readLine();
            Errors.failIf(firstLine == null);
            ModelFinder.Result result;
            if (firstLine.equals("sat")) {
                result = ModelFinder.Result.SAT;
            } else if (firstLine.equals("unsat")){
                result = ModelFinder.Result.UNSAT;
            } else {
                result = ModelFinder.Result.ERROR;
            }
            process.waitFor();
            process.destroy();
        
            return result;
        } catch(IOException e) {
            return ModelFinder.Result.ERROR;
        } catch(InterruptedException e) {
            return ModelFinder.Result.ERROR;
        }
    }
    
    public static void writeSmtLib(Theory theory, BufferedWriter writer) throws IOException {
        List<SExpr> sortDeclarations = generateSortDeclarations(theory);
        List<SExpr> functionDeclarations = generateFunctionDeclarations(theory);
        List<SExpr> constantDeclarations = generateConstantDeclarations(theory);
        List<SExpr> assertions = generateAssertions(theory);
        
        for(SExpr sexpr : sortDeclarations) {
            writer.write(sexpr.toString());
            writer.newLine();
        }
        for(SExpr sexpr : functionDeclarations) {
            writer.write(sexpr.toString());
            writer.newLine();
        }
        for(SExpr sexpr : constantDeclarations) {
            writer.write(sexpr.toString());
            writer.newLine();
        }
        for(SExpr sexpr : assertions) {
            writer.write(sexpr.toString());
            writer.newLine();
        }
    
        writer.write("(check-sat)");
    }
    
    private static Set<Type> sortsDoNotDeclare = new HashSet<>() {{
        add(Type.Bool);
    }};
    
    private static List<SExpr> generateSortDeclarations(Theory theory) {
        return theory.getTypes().stream().filter(
            type -> !sortsDoNotDeclare.contains(type)
        ).map(
            type ->
                new ComExpr(
                    new StrExpr("declare-sort"),
                    new StrExpr(type.toString())
                )
        ).collect(Collectors.toList());
    }
    
    
    private static List<SExpr> generateFunctionDeclarations(Theory theory) {
        List<SExpr> declarations = new ArrayList<>();
        for(FuncDecl funcDecl: theory.getFunctionSymbols()) {
            List<SExpr> argTypeExprs = funcDecl.getArgTypes().stream().map(
                type -> new StrExpr(type.toString())
            ).collect(Collectors.toList());
            declarations.add(
                new ComExpr(
                    new StrExpr("declare-fun"), // Declare as function
                    new StrExpr(funcDecl.getName()), // Function name
                    new ComExpr(argTypeExprs), // Argument types
                    new StrExpr(funcDecl.getResultType().toString()) // Result type
                )
            );
        }
        return declarations;
    }
    
    private static List<SExpr> generateConstantDeclarations(Theory theory) {
        return theory.getConstants().stream().map(
            constant ->
                new ComExpr(
                    new StrExpr("declare-const"),
                    new StrExpr(constant.getName()),
                    new StrExpr(constant.getType().toString())
                )
        ).collect(Collectors.toList());
    }
    
    private static List<SExpr> generateAssertions(Theory theory) {
        SmtExprVisitor toSmtExpr = new SmtExprVisitor();
        return theory.getAxioms().stream().map(
            axiom ->
                new ComExpr(
                    new StrExpr("assert"),
                    toSmtExpr.visit(axiom)
                )
        ).collect(Collectors.toList());
    }
}
