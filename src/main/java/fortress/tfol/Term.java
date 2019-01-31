package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import java.util.Optional;
import java.util.Set;

public abstract class Term {
    
    // Published interface 
    // Term subclasses are not published
    
    public static Optional<Type> typeCheck(Term term, Set<Type> types,
        Set<Var> constants, Set<FuncDecl> functionDeclarations) {
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
    
    public static Var mkVar(String name, Type type) {
        return new Var(name, type);
    }
    
    public static Term mkAnd(List<Term> arguments) {
        return new AndList(arguments);
    }
    public static Term mkAnd(Term t1, Term t2) {
        List<Term> arguments = new ArrayList<>();
        arguments.add(t1);
        arguments.add(t2);
        return mkAnd(arguments);
    }
    
    public static Term mkOr(List<Term> arguments) {
        return new OrList(arguments);
    }
    public static Term mkOr(Term t1, Term t2) {
        List<Term> arguments = new ArrayList<>();
        arguments.add(t1);
        arguments.add(t2);
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
    
    public static Term mkApp(FuncDecl f, List<Term> arguments) {
        return new App(f, arguments);
    }
    public static Term mkApp(FuncDecl f, Term... arguments) {
        List<Term> args = new ArrayList<>();
        for(Term arg : arguments) {
            args.add(arg);
        }
        return mkApp(f, args);
    }
    
    public static Term mkForall(List<Var> vars, Term body) {
        return new Forall(vars, body);
    }
    public static Term mkForall(Var x, Term body) {
        List<Var> vars = new ArrayList<>();
        vars.add(x);
        return mkForall(vars, body);
    }
    
    public static Term mkExists(List<Var> vars, Term body) {
        return new Exists(vars, body);
    }
    public static Term mkExists(Var x, Term body) {
        List<Var> vars = new ArrayList<>();
        vars.add(x);
        return mkExists(vars, body);
    }
    
    public static Term mkDistinct(List<Var> vars) {
        return new Distinct(vars);
    }
    public static Term mkDistinct(Var... vars) {
        List<Var> variables = new ArrayList<>();
        for(Var var : vars) {
            variables.add(var);
        }
        return mkDistinct(variables);
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
