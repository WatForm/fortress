package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.data.ImmutableWrapperList;
import java.util.List;
import java.util.Optional;
import fortress.data.PersistentSet;
import java.util.Set;
import fortress.util.Errors;
import fortress.tfol.visitor.TermVisitor;
import fortress.tfol.visitor.TypeCheckVisitor;
import fortress.tfol.visitor.FreeVariablesVisitor;
import fortress.tfol.visitor.SmtExprVisitor;
import fortress.tfol.visitor.NnfVisitor;
import fortress.sexpr.*;
import java.util.function.Function;

public abstract class Term {
    
    // Published interface 
    // Term subclasses are not published
    
    // Creation operations
    
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
    // To create an annotated var, use Term.mkVar(name).of(type)
    
    // NOTE: Terms should NOT use the identical list/collection/etc given by the user
    // unless it is guaranteed to be immutable - terms could then be mutated
    
    public static Term mkAnd(Term... args) {
        Errors.failIf(args.length < 2);
        return new AndList(ImmutableWrapperList.copyArray(args));
    }
    public static Term mkAnd(List<Term> args) {
        Errors.failIf(args.size() < 2);
        return new AndList(ImmutableWrapperList.copyCollection(args));
    }
    
    public static Term mkOr(Term... args) {
        Errors.failIf(args.length < 2);
        return new OrList(ImmutableWrapperList.copyArray(args));
    }
    public static Term mkOr(List<Term> args) {
        Errors.failIf(args.size() < 2);
        return new OrList(ImmutableWrapperList.copyCollection(args));
    }
    
    public static Term mkNot(Term t) {
        return new Not(t);
    }
    
    public static Term mkImp(Term t1, Term t2) {
        return new Implication(t1, t2);
    }
    
    public static Term mkEq(Term t1, Term t2) {
        return new Eq(t1, t2);
    }
    
    public static Term mkDistinct(List<Term> arguments) {
        Errors.failIf(arguments.size() < 2);
        return new Distinct(ImmutableWrapperList.copyCollection(arguments));
    }
    public static Term mkDistinct(Term... arguments) {
        Errors.failIf(arguments.length < 2);
        return new Distinct(ImmutableWrapperList.copyArray(arguments));
    }
    
    public static Term mkApp(String functionName, Term... arguments) {
        return new App(functionName, ImmutableWrapperList.copyArray(arguments));
    }
    public static Term mkApp(String functionName, List<Term> arguments) {
        return new App(functionName, ImmutableWrapperList.copyCollection(arguments));
    }
    
    public static Term mkForall(List<AnnotatedVar> vars, Term body) {
        ImmutableList<AnnotatedVar> varsCopy = ImmutableWrapperList.copyCollection(vars);
        return new Forall(varsCopy, body);
    }
    public static Term mkForall(AnnotatedVar x, Term body) {
        ImmutableList<AnnotatedVar> vars = ImmutableList.of(x);
        return new Forall(vars, body);
    }
    
    public static Term mkExists(List<AnnotatedVar> vars, Term body) {
        ImmutableList<AnnotatedVar> varsCopy = ImmutableWrapperList.copyCollection(vars);
        return new Exists(varsCopy, body);
    }
    public static Term mkExists(AnnotatedVar x, Term body) {
        ImmutableList<AnnotatedVar> vars = ImmutableList.of(x);
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
    
    // Not published
    
    // TODO should freeVars, typecheck be a method of Term or Signature?
    
    // TODO: should freeVarConstSymbols be published? TptpToFortress makes good use of it
    // -- TptpToFortress could avoid it, but it would be more difficult
    
    // Returns the set of Vars that appear unquantified in this term.
    // This only looks at syntax without respect to a given signature,
    // so it could also include what are intended to be constants.
    public Set<Var> freeVarConstSymbols() {
        return new FreeVariablesVisitor().visit(this);
    }
    
    // Returns the set of free variables of this term with respect
    // to the given signature.
    public Set<Var> freeVars(Signature signature) {
        Set<Var> freeVars = freeVarConstSymbols();
        freeVars.removeAll(signature.getConstants());
        return freeVars;
    }
    
    // Returns an optional containing the term's type with repsect to the
    // given signature, or an empty optional if typechecking fails.
    // Note that a term that is not closed cannot typecheck correctly.
    public Optional<Type> typecheck(Signature signature) {
        TypeCheckVisitor visitor = new TypeCheckVisitor(signature);
        return visitor.visit(this);
    }
    
    public Term nnf(Signature sig) {
        NnfVisitor nnf = new NnfVisitor(sig); 
        return nnf.visit(this);
    }
    
    public SExpr toSmtExpr() {
        return new SmtExprVisitor().visit(this);
    }
    
    
    // TODO negation normal form with =? = can be bi-implication
    // need to eliminate <=> but checking if = is <=> requires typechecking
    // So maybe it needs to be done at the theory level?
    
    // NOTE: 
    // We shouldn't provide these tools to the user
    // One step of the theory should be to replace = by iff where possible
    

    // public Term negationNormalForm() {
    //     ???
    // }
    // 
    // // Returns a logically equivalent formula 
    // public Term prenexNormalForm() {
    //     Term t = refreshBoundVariables();
    //     ???
    // }
    // 
    // public Term withTypeSubstitution(Map<Type, Type> typeSubstitution) {
    //     ???
    // }
    // 
    // public boolean alphaEquivalent(Term other) {
    //     ???
    // } 
    // 
    // public Term refreshBoundVariables(NameGenerator generator) {
    //     ???
    // }
    // 
    // public Term substituteVars(Map<Var, Term> )
    
    // Given an object, guaranteed to be a term of the the same subtype, return
    // whether they are equal to this
    protected abstract boolean innerEquals(Object other);
    
    
    
    // List of numbers to be included when computing the hashCode
    // TODO consider making this an int[] instead for efficiency
    protected abstract List<Integer> innerHashNumbers();

    public abstract <T> T accept(TermVisitor<T> visitor);
    
    // For testing only
    @Override
    public String toString() {
        return new SmtExprVisitor().visit(this).toString();
    }
}
