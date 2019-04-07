package fortress.outputs;

import com.microsoft.z3.*;

import java.util.Map;
import java.util.HashMap;
import java.util.LinkedList;
import java.lang.RuntimeException;
import java.util.stream.Collectors;
import java.util.Optional;

import fortress.tfol.*;
import fortress.tfol.operations.TermVisitorWithTypeContext;
import fortress.util.Pair;

public class TheoryToZ3Java {
    private final Theory theory;
    private final Context context;
    
    private final Map<Type, Sort> sortConversions;
    private final Map<String, com.microsoft.z3.FuncDecl> functionConversions;
    private final Map<String, com.microsoft.z3.FuncDecl> constantConversions;
    
    private TermToZ3Visitor termVisitor;
    
    // Precondition: theory must be typechecked and all declarations must
    // be internally consistent
    public TheoryToZ3Java(Theory theory) {
        HashMap<String, String> config = new HashMap<>();
        config.put("model", "true"); // turn on model generation
        this.theory = theory;
        this.context = new Context(config);
        
        this.sortConversions = new HashMap<>();
        this.functionConversions = new HashMap<>();
        this.constantConversions = new HashMap<>();
        termVisitor = new TermToZ3Visitor();
    }
    
    public Pair<Context, Solver> convert() {
        // Put in sort conversions
        sortConversions.put(Type.Bool(), context.getBoolSort());
        for(Type t : theory.getTypes()) {
            // TODO more elegant handling of built-in types
            if(!t.equals(Type.Bool())) {
                Sort s = context.mkUninterpretedSort(t.getName());
                sortConversions.put(t, s);
            }
        }
        
        // Put in function conversions
        for(fortress.tfol.FuncDecl fortressDecl : theory.getFunctionDeclarations()) {
            Sort[] argSorts = fortressDecl.getArgTypes().stream().map(this::lookupSortConversion).toArray(Sort[]::new);
            Sort resultSort = lookupSortConversion(fortressDecl.getResultType());
            com.microsoft.z3.FuncDecl z3Decl = context.mkFuncDecl(fortressDecl.getName(), argSorts, resultSort);
            functionConversions.put(fortressDecl.getName(), z3Decl);
        }
        
        // Put in constant conversions
        for(AnnotatedVar fortressDecl : theory.getConstants()) {
            Sort sort = lookupSortConversion(fortressDecl.getType());
            com.microsoft.z3.FuncDecl z3Decl = context.mkConstDecl(fortressDecl.getName(), sort);
            functionConversions.put(fortressDecl.getName(), z3Decl);
        }
        
        // Convert axioms and add to solver
        Solver solver = context.mkSolver("UF"); // Logic of uninterpreted functions
        for(Term axiom : theory.getAxioms()) {
            // TODO is there a simple way to avoid casting here?
            // Assuming our implementation is correct and preconditions are
            // met, this should not fail... However casting is still frowned upon
            BoolExpr formula = (BoolExpr) termVisitor.visit(axiom);
            solver.add(formula);
        }
        return new Pair<>(context, solver);
    }
    
    private Sort lookupSortConversion(Type t) {
        if(!sortConversions.containsKey(t)) {
            throw new RuntimeException("Could not find declaration for type " + t.toString());
        }
        return sortConversions.get(t);
    }
    
    private com.microsoft.z3.FuncDecl lookupFuncDecl(String name) {
        if(!functionConversions.containsKey(name)) {
            throw new RuntimeException("Could not find declaration for function " + name);
        }
        return functionConversions.get(name);
    }
    
    private class TermToZ3Visitor extends TermVisitorWithTypeContext<Expr> {
        
        private TermToZ3Visitor() {
            super(theory.getSignature());
        }
        
        private Type lookupVarType(Var variable) {
            Optional<Type> typeMaybe = lookupType(variable);
            
            if(!typeMaybe.isPresent()) {
                // Error, there must be something wrong with the theory
                throw new RuntimeException("Could not find type of variable " + variable.toString());
            }
            return typeMaybe.get();
        }
        
        @Override
        public Expr visitTop(Top term) {
            return context.mkTrue();
        }
        
        @Override
        public Expr visitBottom(Bottom term) {
            return context.mkFalse();
        }
        
        @Override
        public Expr visitVar(Var variable) {
            Type t = lookupVarType(variable);
            Sort s = lookupSortConversion(t);
            return context.mkConst(variable.getName(), s);
        }
        
        @Override
        public Expr visitNot(Not term) {
            // TODO is there a simple way to avoid casting here?
            // Assuming our implementation is correct and preconditions are
            // met, this should not fail... However casting is still frowned upon
            BoolExpr body = (BoolExpr) visit(term.getBody());
            return context.mkNot(body);
        }
        
        @Override
        public Expr visitAndList(AndList term) {
            // TODO is there a simple way to avoid casting here?
            BoolExpr[] args = term.getArguments().stream().map(
                (Term t) -> (BoolExpr) visit(t)
            ).toArray(BoolExpr[]::new);
            return context.mkAnd(args);
        }
        
        @Override
        public Expr visitOrList(OrList term) {
            // TODO is there a simple way to avoid casting here?
            BoolExpr[] args = term.getArguments().stream().map(
                (Term t) -> (BoolExpr) visit(t)
            ).toArray(BoolExpr[]::new);
            return context.mkOr(args);
        }
        
        @Override
        public Expr visitDistinct(Distinct term) {
            Expr[] args = term.getArguments().stream().map(
                (Term t) -> visit(t)
            ).toArray(Expr[]::new);
            return context.mkDistinct(args);
        }
        
        @Override
        public Expr visitImplication(Implication term) {
            // TODO is there a simple way to avoid casting here?
            return context.mkImplies(
                (BoolExpr) visit(term.getLeft()),
                (BoolExpr) visit(term.getRight())
            );
        }
        
        @Override
        public Expr visitIff(Iff term) {
            return context.mkEq(
                visit(term.getLeft()),
                visit(term.getRight())
            );
        }
        
        @Override
        public Expr visitEq(Eq term) {
            return context.mkEq(
                visit(term.getLeft()),
                visit(term.getRight())
            );
        }
        
        @Override
        public Expr visitApp(App term) {
            com.microsoft.z3.FuncDecl fdecl = lookupFuncDecl(term.getFunctionName());
            Expr[] args = term.getArguments().stream().map(
                (Term t) -> visit(t)
            ).toArray(Expr[]::new);
            return fdecl.apply(args);
        }
        
        @Override
        public Expr visitExistsInner(Exists term) {
            // TODO will having no patterns change performance?
            // TODO look at C++ docs if Java docs doesn't have the info
            
            Expr[] vars = term.getVars().stream().map(
                (AnnotatedVar av) -> visit(av.getVar())
            ).toArray(Expr[]::new);
            Expr body = visit(term.getBody());
            
            return context.mkExists(
                vars,
                body,
                0, // Default weight of 0
                null, // No patterns
                null, // No anti-patterns
                null, // No symbol to track quantifier
                null // No symbol to track skolem constants
            );
        }
        
        @Override
        public Expr visitForallInner(Forall term) {
            // TODO will having no patterns change performance?
            // TODO look at C++ docs if Java docs doesn't have the info
            
            Expr[] vars = term.getVars().stream().map(
                (AnnotatedVar av) -> visit(av.getVar())
            ).toArray(Expr[]::new);
            Expr body = visit(term.getBody());
            
            return context.mkForall(
                vars,
                body,
                0, // Default weight of 0
                null, // No patterns
                null, // No anti-patterns
                null, // No symbol to track quantifier
                null // No symbol to track skolem constants
            );
        }
    }
}
