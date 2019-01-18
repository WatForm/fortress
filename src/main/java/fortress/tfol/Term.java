package fortress.tfol;

import java.util.List;
import java.util.ArrayList;

public abstract class Term {
    
    // Published interface 
    // Term subclasses are not published
    
    public static Term mkVar(String name, Type type) {
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
    
    public static Term mkForall(List<Var> vars, Term body) {
        return new Forall(vars, body);
    }
    
    public static Term mkExists(List<Var> vars, Term body) {
        return new Exists(vars, body);
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
    protected abstract List<Integer> innerHashNumbers();

}
