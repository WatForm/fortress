package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import java.util.Optional;
import java.util.Set;
import fortress.util.Errors;

public abstract class Term {
    
    // Published interface 
    // Term subclasses are not published
    
    // TODO sepearate out this precondition into a function
    // TODO should typecheck also check consistency? Efficiency concerns for Theory
    // Precondition: types, constants, and function declarations must together
    // be consistent
    //      - no different functions or constants of the same name)
    //      - constants, functions must use types that exist in the types set
    public static Optional<Type> typeCheck(Term term, Set<Type> types,
        Set<AnnotatedVar> constants, Set<FuncDecl> functionDeclarations) {
        TypeCheckVisitor typeChecker = new TypeCheckVisitor(types, constants, functionDeclarations);
        return typeChecker.visit(term);
    }
    
    public static Set<Var> freeVariables(Term term) {
        FreeVariablesVisitor freeVarsCollector = new FreeVariablesVisitor();
        return freeVarsCollector.visit(term);
    }
    
    public static Term mkTop() {
        return new Top();
    }
    
    public static Term mkBottom() {
        return new Bottom();
    }
    
    public static Var mkVar(String name) {
        return new Var(name);
    }
    
    // NOTE: There is no mkAnnotatedVar because we do not want people to think
    // that AnnotatedVar is a Term
    // To create an annotated var, use Term.mkVar("x").of(type)
    
    public static Term mkAnd(List<Term> arguments) {
        Errors.failIf(arguments.size() < 2);
        return new AndList(arguments);
    }
    public static Term mkAnd(Term... args) {
        Errors.failIf(args.length < 2);
        List<Term> arguments = new ArrayList<>();
        for(Term arg : args) {
            arguments.add(arg);
        }
        return mkAnd(arguments);
    }
    
    public static Term mkOr(List<Term> arguments) {
        Errors.failIf(arguments.size() < 2);
        return new OrList(arguments);
    }
    public static Term mkOr(Term... args) {
        Errors.failIf(args.length < 2);
        List<Term> arguments = new ArrayList<>();
        for(Term arg : args) {
            arguments.add(arg);
        }
        return mkOr(arguments);
    }
    
    public static Term mkNot(Term t) {
        return new Not(t);
    }
    
    public static Term mkImp(Term t1, Term t2) {
        return new Implication(t1, t2);
    }
    
    public static Term mkIff(Term t1, Term t2) {
        return new Iff(t1, t2);
    }
    
    public static Term mkEq(Term t1, Term t2) {
        return new Eq(t1, t2);
    }
    
    public static Term mkApp(String functionName, List<Term> arguments) {
        return new App(functionName, arguments);
    }
    public static Term mkApp(String functionName, Term... arguments) {
        List<Term> args = new ArrayList<>();
        for(Term arg : arguments) {
            args.add(arg);
        }
        return mkApp(functionName, args);
    }
    
    public static Term mkForall(List<AnnotatedVar> vars, Term body) {
        return new Forall(vars, body);
    }
    public static Term mkForall(AnnotatedVar x, Term body) {
        List<AnnotatedVar> vars = new ArrayList<>();
        vars.add(x);
        return mkForall(vars, body);
    }
    
    public static Term mkExists(List<AnnotatedVar> vars, Term body) {
        return new Exists(vars, body);
    }
    public static Term mkExists(AnnotatedVar x, Term body) {
        List<AnnotatedVar> vars = new ArrayList<>();
        vars.add(x);
        return mkExists(vars, body);
    }
    
    public static Term mkDistinct(List<Term> arguments) {
        return new Distinct(arguments);
    }
    public static Term mkDistinct(Term... args) {
        List<Term> arguments = new ArrayList<>();
        for(Term arg : args) {
            arguments.add(arg);
        }
        return mkDistinct(arguments);
    }
    
    @Override
    public boolean equals(Object other) {
        // Template method design
        if(this == other) {
            return true;
        }
        if(null == other) {
            return false;
        }
        if(this.getClass() != other.getClass()) {
            return false;
        }
        return innerEquals(other);
    }
    
    // Given an object, guaranteed to be a term of the the same subtype, return
    // whether they are equal to this
    protected abstract boolean innerEquals(Object other);
    
    @Override
    public int hashCode() {
        // Template method design
        int prime = 31;
        int result = 1;
        for(int num : innerHashNumbers()) {
            result = result * prime + num;
        }
        return result;
    }
    
    // List of numbers to be included when computing the hashCode
    // TODO consider making this an int[] instead for efficiency
    protected abstract List<Integer> innerHashNumbers();

    protected abstract <T> T accept(TermVisitor<T> visitor);
    
    // For testing only
    @Override
    public String toString() {
        return new SmtExprVisitor().visit(this).toString();
    }
}
