package fortress.tfol;

import com.microsoft.z3.*;
import java.util.Map;
import java.util.HashMap;
import java.util.LinkedList;
import java.lang.RuntimeException;
import java.util.stream.Collectors;
import java.util.Optional;

public class TheoryToZ3Java implements TermVisitor<Expr>{
    private Theory theory;
    private Context context;
    
    private LinkedList<AnnotatedVar> typeContext;
    
    private Map<Type, Sort> sortConversions;
    private Map<String, com.microsoft.z3.FuncDecl> functionConversions;
    private Map<String, com.microsoft.z3.FuncDecl> constantConversions;
    
    // Precondition: theory must be typechecked and all declarations must
    // be internally consistent
    public TheoryToZ3Java(Theory theory) {
        HashMap<String, String> config = new HashMap();
        config.put("model", "true"); // turn on model generation
        this.theory = theory;
        this.context = new Context(config);
        this.typeContext = new LinkedList();
        
        this.sortConversions = new HashMap();
        this.functionConversions = new HashMap();
        this.constantConversions = new HashMap();
    }
    
    public Solver convert() {
        // Put in sort conversions
        sortConversions.put(Type.Bool, context.getBoolSort());
        for(Type t : theory.getTypes()) {
            // TODO more elegant handling of built-in types
            if(!t.equals(Type.Bool)) {
                Sort s = context.mkUninterpretedSort(t.toString());
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
            BoolExpr formula = (BoolExpr) visit(axiom);
            solver.add(formula);
        }
        return solver;
    }
    
    private Type lookupVarType(Var variable) {
        // Look up in type context first
        for(AnnotatedVar av : typeContext) {
            if(av.getName().equals(variable.getName())) {
                return av.getType();
            }
        }
        
        // If it is not in the context it must be in the constants list
        for(AnnotatedVar av : theory.getConstants()) {
            if(av.getName().equals(variable.getName())) {
                return av.getType();
            }
        }
        
        // Error, there must be something wrong with the theory
        throw new RuntimeException("Could not find type of variable " + variable.toString());
    }
    
    private Sort lookupSortConversion(Type t) {
        if(!sortConversions.containsKey(t)) {
            throw new RuntimeException("Could not find declaration for type " + t.toString());
        }
        return sortConversions.get(t);
    }
    
    private com.microsoft.z3.FuncDecl lookupFuncDecl(String name) {
        if(!sortConversions.containsKey(name)) {
            throw new RuntimeException("Could not find declaration for function " + name);
        }
        return functionConversions.get(name);
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
    
    public Expr visitNot(Not term) {
        // TODO is there a simple way to avoid casting here?
        // Assuming our implementation is correct and preconditions are
        // met, this should not fail... However casting is still frowned upon
        BoolExpr body = (BoolExpr) visit(term.getBody());
        return context.mkNot(body);
    }
    
    public Expr visitAndList(AndList term) {
        // TODO is there a simple way to avoid casting here?
        BoolExpr[] args = term.getArguments().stream().map(
            (Term t) -> (BoolExpr) visit(t)
        ).toArray(BoolExpr[]::new);
        return context.mkAnd(args);
    }
    
    public Expr visitOrList(OrList term) {
        // TODO is there a simple way to avoid casting here?
        BoolExpr[] args = term.getArguments().stream().map(
            (Term t) -> (BoolExpr) visit(t)
        ).toArray(BoolExpr[]::new);
        return context.mkOr(args);
    }
    
    public Expr visitDistinct(Distinct term) {
        Expr[] args = term.getArguments().stream().map(
            (Term t) -> visit(t)
        ).toArray(Expr[]::new);
        return context.mkDistinct(args);
    }
    
    public Expr visitIff(Iff term) {
        // TODO is there a simple way to avoid casting here?
        return context.mkIff(
            (BoolExpr) visit(term.getLeft()),
            (BoolExpr) visit(term.getRight())
        );
    }
    
    public Expr visitImplication(Implication term) {
        // TODO is there a simple way to avoid casting here?
        return context.mkImplies(
            (BoolExpr) visit(term.getLeft()),
            (BoolExpr) visit(term.getRight())
        );
    }
    
    public Expr visitEq(Eq term) {
        return context.mkEq(
            visit(term.getLeft()),
            visit(term.getRight())
        );
    }
    
    public Expr visitApp(App term) {
        com.microsoft.z3.FuncDecl fdecl = lookupFuncDecl(term.getFunctionName());
        Expr[] args = term.getArguments().stream().map(
            (Term t) -> visit(t)
        ).toArray(Expr[]::new);
        return fdecl.apply(args);
    }
    
    public Expr visitExists(Exists term) {
        // TODO will having no patterns change performance?
        // TODO look at C++ docs if Java docs doesn't have the info
        
        // Put annotated variables on typeContext stack
        // This needs to be there since Z3 requires the uses of these quantifed
        // variables to be annotated with their types
        for(AnnotatedVar av : term.getVars()) {
            typeContext.addFirst(av);
        }
        
        Expr[] vars = term.getVars().stream().map(
            (AnnotatedVar av) -> visit(av.getVar())
        ).toArray(Expr[]::new);
        Expr body = visit(term.getBody());
        
        // Pop typeContext stack
        for(AnnotatedVar av : term.getVars()) {
            typeContext.removeFirst();
        }
        
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
    
    public Expr visitForall(Forall term) {
        // TODO will having no patterns change performance?
        // TODO look at C++ docs if Java docs doesn't have the info
        
        // Put annotated variables on typeContext stack
        // This needs to be there since Z3 requires the uses of these quantifed
        // variables to be annotated with their types
        for(AnnotatedVar av : term.getVars()) {
            typeContext.addFirst(av);
        }
        
        Expr[] vars = term.getVars().stream().map(
            (AnnotatedVar av) -> visit(av.getVar())
        ).toArray(Expr[]::new);
        Expr body = visit(term.getBody());
        
        // Pop typeContext stack
        for(AnnotatedVar av : term.getVars()) {
            typeContext.removeFirst();
        }
        
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
