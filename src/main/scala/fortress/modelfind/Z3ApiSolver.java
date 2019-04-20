package fortress.modelfind;

import java.io.*;
import java.util.Map;
import java.util.List;
import java.util.Arrays;
import java.util.HashMap;
import java.util.regex.*;
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
        FiniteModel model = new FiniteModel();
        Map<Expr, DomainElement> typeMappings = new HashMap<>();
        Map<Sort, List<Expr>> domains = new HashMap<>();
        Map<String, Type> types = new HashMap<>();
        for (Type type : theory.getTypes())
            types.put(type.getName(), type);
        for (Sort sort : lastModel.getSorts()) {
            String typeName = sort.toString();
            if (types.get(typeName) != null)
                domains.put(sort, Arrays.asList(lastModel.getSortUniverse(sort)));
        }
        Map<String, AnnotatedVar> constants = new HashMap<>();
        for (AnnotatedVar v : theory.getConstants())
            constants.put(v.getName(), v);
        for (com.microsoft.z3.FuncDecl z3Decl : lastModel.getConstDecls()) {
            String constantName = z3Decl.getName().toString();
            if (constantName.charAt(0) == '@') {
                Matcher m = java.util.regex.Pattern.compile("\\p{L}").matcher(constantName);
                if (m.find()) {
                    int typePosition = m.start();
                    int index = Integer.parseInt(constantName.substring(1, typePosition));
                    Type sort = types.get(constantName.substring(typePosition));
                    typeMappings.put(lastModel.getConstInterp(z3Decl), Term.mkDomainElement(index, sort));
                }
            }
        }    
        for (com.microsoft.z3.FuncDecl z3Decl : lastModel.getConstDecls()) {
            AnnotatedVar v = constants.get(z3Decl.getName().toString());
            if (v != null)
                model.addConstantMapping(v, typeMappings.get(lastModel.getConstInterp(z3Decl)));    
        }
        Map<fortress.tfol.FuncDecl, Map<List<Var>, Var>> functionMappings = new HashMap<>();
        Map<String, fortress.tfol.FuncDecl> functions = new HashMap<>();
        for (fortress.tfol.FuncDecl f : theory.getFunctionDeclarations())
            functions.put(f.getName(), f);
        for (com.microsoft.z3.FuncDecl z3Decl : lastModel.getFuncDecls()) {
            fortress.tfol.FuncDecl f = functions.get(z3Decl.getName().toString());
            if (f != null) {
                List<List<Expr>> toProduct = new ArrayList<>();
                for (Sort type : z3Decl.getDomain())
                    toProduct.add(domains.get(type));
                CartesianProduct<Expr> argumentLists = new CartesianProduct<>(toProduct);
                for(List<Expr> argumentList : argumentLists) {
                    List<DomainElement> args = argumentList.stream().map(s -> typeMappings.get(s)).collect(Collectors.toList());
                    Expr returnExpr = lastModel.evaluate(z3Decl.apply(argumentList.stream().toArray(Expr[]::new)), true);
                    if (z3Decl.getRange() instanceof BoolSort) {
                        if (returnExpr.isTrue())
                            model.addFunctionMapping(f, args, Term.mkDomainElement(1, Type.Bool()));
                        else
                            model.addFunctionMapping(f, args, Term.mkDomainElement(0, Type.Bool()));
                    } else
                        model.addFunctionMapping(f, args, typeMappings.get(returnExpr));
                }
            }
        }
        return model;
    }
}