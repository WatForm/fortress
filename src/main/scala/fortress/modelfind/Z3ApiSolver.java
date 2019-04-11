package fortress.modelfind;

import java.io.*;
import java.util.Map;
import java.util.List;
import java.util.Arrays;
import java.util.HashMap;
import java.util.ArrayList;
import java.util.stream.Collectors;

import fortress.tfol.*;
import fortress.outputs.*;
import fortress.util.Pair;
import fortress.util.StopWatch;
import fortress.util.Errors;
import fortress.data.CartesianProduct;

import com.microsoft.z3.*;

public class Z3ApiSolver extends SolverTemplate {
    private Model lastModel = null;
    private Context context = null;
    private Solver solver = null;
    
    @Override
    public boolean canAttemptSolving(Theory theory) {
        return true;
    }
    
    @Override
    protected void convertTheory(Theory theory, Writer log) { 
        Pair<Context, Solver> pair = new TheoryToZ3Java(theory).convert();
        context = pair.left;
        solver = pair.right;
    }
    
    @Override
    protected void updateTimeout(int remainingMillis) {
        Errors.assertion(null != context);
        Errors.assertion(null != solver);
        
        Params params = context.mkParams();
        params.add("timeout", remainingMillis);
        solver.setParameters(params);
    }
    
    @Override
    protected ModelFinder.Result runSolver(Writer log) throws IOException {
        Errors.assertion(null != context);
        Errors.assertion(null != solver);
        
        Status status = solver.check();
        lastModel = null;
        switch(status) {
            case UNKNOWN:
                // TODO timeout errors
                log.write("UKNOWN (" + solver.getReasonUnknown() + ").\n");
                if(solver.getReasonUnknown().equals("timeout")
                        || solver.getReasonUnknown().equals("canceled")) {
                    return ModelFinder.Result.TIMEOUT;
                }
                return ModelFinder.Result.UNKNOWN;
                // break;
            case SATISFIABLE:
                lastModel = solver.getModel();
                log.write("SAT.\n");
                return ModelFinder.Result.SAT;
                // break;
            case UNSATISFIABLE:
                log.write("UNSAT.\n");
                return ModelFinder.Result.UNSAT;
                // break;
            default:
                throw new RuntimeException("Unexpected solver result " + status.toString());
        }
    }
    
    // Temporary method -- will be changed
    public String getStringModel() {
        if (lastModel == null)
            return "ERROR - NO MODEL";
        return lastModel.toString();
    }

    public FiniteModel getModel(Theory theory) {
        //TODO: edit to fit FiniteModel
        // find mappings for types
        Map<Type, List<Var>> typeMappings = new HashMap<>();
        Map<Sort, List<Expr>> domains = new HashMap<>();
        Map<String, Type> types = new HashMap<>();
        for (Type type : theory.getTypes())
            types.put(type.getName(), type);
        for(Sort sort : lastModel.getSorts()) {
            String typeName = sort.toString();
            Type type = types.get(typeName);
            if (type != null) {
                List<Expr> vars = Arrays.asList(lastModel.getSortUniverse(sort));
                typeMappings.put(type, vars.stream().map(s -> Term.mkVar(s.toString())).collect(Collectors.toList()));
                domains.put(sort, vars);
            }
        }

        // find mappings for constants
        Map<AnnotatedVar, Var> constantMappings = new HashMap<>();
        Map<String, AnnotatedVar> constants = new HashMap<>();
        for (AnnotatedVar v : theory.getConstants())
            constants.put(v.getName(), v);
        for (com.microsoft.z3.FuncDecl z3Decl : lastModel.getConstDecls()) {
            AnnotatedVar v = constants.get(z3Decl.getName().toString());
            if (v != null)
                constantMappings.put(v, Term.mkVar(lastModel.getConstInterp(z3Decl).toString()));
        }        

        // find mappings for functions
        Map<fortress.tfol.FuncDecl, Map<List<Var>, Var>> functionMappings = new HashMap<>();
        Map<String, fortress.tfol.FuncDecl> functions = new HashMap<>();
        for (fortress.tfol.FuncDecl f : theory.getFunctionDeclarations())
            functions.put(f.getName(), f);
        for (com.microsoft.z3.FuncDecl z3Decl : lastModel.getFuncDecls()) {
            fortress.tfol.FuncDecl f = functions.get(z3Decl.getName().toString());
            if (f != null) {
                Map<List<Var>, Var> argumentMappings = new HashMap<>();
                List<List<Expr>> toProduct = new ArrayList<>();
                for (Sort type : z3Decl.getDomain())
                    toProduct.add(domains.get(type));
                CartesianProduct<Expr> argumentLists = new CartesianProduct<>(toProduct);
                for(List<Expr> argumentList : argumentLists) {
                    List<Var> args = argumentList.stream().map(s -> Term.mkVar(s.toString())).collect(Collectors.toList());
                    Expr returnExpr = lastModel.evaluate(z3Decl.apply(argumentList.stream().toArray(Expr[]::new)), true);
                    if (z3Decl.getRange() instanceof BoolSort) {
                        if (returnExpr.isTrue())
                            argumentMappings.put(args, Term.mkVar("True"));
                        else
                            argumentMappings.put(args, Term.mkVar("False"));
                    } else
                        argumentMappings.put(args, Term.mkVar(returnExpr.toString()));
                }
                functionMappings.put(f, argumentMappings);
            }
        }

        // print model (remove later)
        for (Map.Entry<Type, List<Var>> entry : typeMappings.entrySet()) {
            System.out.print(entry.getKey().getName() + ": ");
            for (Var v : entry.getValue())
                System.out.print(v.getName() + " ");
            System.out.println();
        }
        for (Map.Entry<AnnotatedVar, Var> entry : constantMappings.entrySet()) {
            System.out.println(entry.getKey().getName() + ": " + entry.getValue().getName());
        }
        for (Map.Entry<fortress.tfol.FuncDecl, Map<List<Var>, Var>> entry : functionMappings.entrySet()) {
            System.out.println(entry.getKey().getName() + ":");
            for (Map.Entry<List<Var>, Var> args : entry.getValue().entrySet()) {
                for (Var v : args.getKey())
                    System.out.print(v.getName() + " ");
                System.out.println("-> "+args.getValue().getName());
            }
        }
        return Errors.<FiniteModel>notImplemented();
    }
}
