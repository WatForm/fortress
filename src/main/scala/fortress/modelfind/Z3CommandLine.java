package fortress.modelfind;

import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import fortress.sexpr.SExpr;
import java.util.stream.Collectors;
import java.io.*;
import fortress.util.Errors;
import fortress.tfol.*;

public class Z3CommandLine implements SolverStrategy {
    
    @Override
    public boolean canAttemptSolving(Theory theory) {
        return true;
    }
    
    public ModelFinder.Result solve(Theory theory, int timeout, Writer log) throws IOException {
        return Errors.<ModelFinder.Result>notImplemented();
        // // TODO need more robust error handling
        // try {
        //     File tempOutputFile = File.createTempFile("fortress", ".smt");
        //     BufferedWriter writer = new BufferedWriter(new FileWriter(tempOutputFile));
        //     writeSmtLib(theory, writer);
        //     writer.flush();
        //     writer.close();
        // 
        //     String command = "z3 -smt2 -memory:2500 -T:2000 ";
        //     Process process = Runtime.getRuntime().exec(command + tempOutputFile.getAbsolutePath());
        //     BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
        //     if(null == reader) {
        //         throw new IOException();
        //     }
        //     String firstLine = reader.readLine();
        //     if(firstLine == null) {
        //         throw new IOException();
        //     }
        //     ModelFinder.Result result;
        //     if (firstLine.equals("sat")) {
        //         result = ModelFinder.Result.SAT;
        //     } else if (firstLine.equals("unsat")){
        //         result = ModelFinder.Result.UNSAT;
        //     } else {
        //         result = ModelFinder.Result.ERROR;
        //     }
        //     process.waitFor();
        //     process.destroy();
        // 
        //     return result;
        // } catch(IOException e) {
        //     return ModelFinder.Result.ERROR;
        // } catch(InterruptedException e) {
        //     return ModelFinder.Result.ERROR;
        // }
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
        add(Type.Bool());
    }};
    
    private static List<SExpr> generateSortDeclarations(Theory theory) {
        return theory.getTypes().stream().filter(
            type -> !sortsDoNotDeclare.contains(type)
        ).map(
            type ->
                SExpr.mkList(
                    SExpr.mkAtom("declare-sort"),
                    SExpr.mkAtom(type.getName())
                )
        ).collect(Collectors.toList());
    }
    
    
    private static List<SExpr> generateFunctionDeclarations(Theory theory) {
        List<SExpr> declarations = new ArrayList<>();
        for(FuncDecl funcDecl: theory.getFunctionDeclarations()) {
            List<SExpr> argTypeExprs = funcDecl.getArgTypes().stream().map(
                type -> SExpr.mkAtom(type.getName())
            ).collect(Collectors.toList());
            declarations.add(
                SExpr.mkList(
                    SExpr.mkAtom("declare-fun"), // Declare as function
                    SExpr.mkAtom(funcDecl.getName()), // Function name
                    SExpr.mkList(argTypeExprs), // Argument types
                    SExpr.mkAtom(funcDecl.getResultType().toString()) // Result type
                )
            );
        }
        return declarations;
    }
    
    private static List<SExpr> generateConstantDeclarations(Theory theory) {
        return theory.getConstants().stream().map(
            constant ->
                SExpr.mkList(
                    SExpr.mkAtom("declare-const"),
                    SExpr.mkAtom(constant.getName()),
                    SExpr.mkAtom(constant.getType().toString())
                )
        ).collect(Collectors.toList());
    }
    
    private static List<SExpr> generateAssertions(Theory theory) {
        return theory.getAxioms().stream().map(
            axiom ->
                SExpr.mkList(
                    SExpr.mkAtom("assert"),
                    axiom.toSmtExpr()
                )
        ).collect(Collectors.toList());
    }

    public Interpretation getInstance(Theory theory) {
        return Errors.<Interpretation>notImplemented();
    }
}
