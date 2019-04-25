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


    public Interpretation getInstance(Theory theory) {
        // TODO builtin types
        Interpretation model = new Interpretation();
        Signature sig = theory.getSignature();
        Map<Expr, DomainElement> typeMappings = new HashMap<>();
        Map<Sort, List<Expr>> domains = new HashMap<>();
        for (Sort sort : lastModel.getSorts()) {
            if (sig.hasType(Type.mkTypeConst(sort.getName().toString())))
                domains.put(sort, Arrays.asList(lastModel.getSortUniverse(sort)));
        }
        for (com.microsoft.z3.FuncDecl z3Decl : lastModel.getConstDecls()) {
            String constantName = z3Decl.getName().toString();
            if (constantName.charAt(0) == '@') {
                String typeName = z3Decl.getRange().getName().toString();
                int index = Integer.parseInt(constantName.substring(1, constantName.length()-typeName.length()));
                typeMappings.put(lastModel.getConstInterp(z3Decl), Term.mkDomainElement(index, Type.mkTypeConst(typeName)));
            }
        }    
        for (com.microsoft.z3.FuncDecl z3Decl : lastModel.getConstDecls())
            sig.queryConstantJava(Term.mkVar(z3Decl.getName().toString())).ifPresent(v -> model.addConstantMapping(v, typeMappings.get(lastModel.getConstInterp(z3Decl))));
        for (com.microsoft.z3.FuncDecl z3Decl : lastModel.getFuncDecls()) {
            sig.queryUninterpretedFunctionJava(z3Decl.getName().toString()).ifPresent( f -> {
                List<List<Expr>> toProduct = new ArrayList<>();
                for (Sort type : z3Decl.getDomain())
                    toProduct.add(domains.get(type));
                CartesianProduct<Expr> argumentLists = new CartesianProduct<>(toProduct);
                for(List<Expr> argumentList : argumentLists) {
                    List<DomainElement> args = argumentList.stream().map(s -> typeMappings.get(s)).collect(Collectors.toList());
                    Expr returnExpr = lastModel.evaluate(z3Decl.apply(argumentList.stream().toArray(Expr[]::new)), true);
                    if (z3Decl.getRange() instanceof BoolSort) {
                        if (returnExpr.isTrue())
                            model.addFunctionMapping(f, args, Term.mkDomainElement(2, Type.Bool()));
                        else
                            model.addFunctionMapping(f, args, Term.mkDomainElement(1, Type.Bool()));
                    } else
                        model.addFunctionMapping(f, args, typeMappings.get(returnExpr));
                }
            });
        }
        return model;
    }
}
