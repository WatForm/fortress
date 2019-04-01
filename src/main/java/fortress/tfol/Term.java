package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.data.ImmutableWrapperList;
import java.util.List;
import java.util.Optional;
import fortress.data.PersistentSet;
import java.util.Set;
import fortress.util.Errors;
import fortress.tfol.operations.*;
import fortress.data.TypeCheckException;
import java.util.stream.Collectors;
import fortress.sexpr.*;
import java.util.function.Function;
import fortress.data.Either;
import fortress.data.NameGenerator;
import fortress.outputs.*;
import java.util.Map;

// NOTE: There is no mkAnnotatedVar because we do not want people to think
// that AnnotatedVar is a Term
// To create an annotated var, use Term.mkVar(name).of(type)

// NOTE: Terms should NOT use the identical list/collection/etc given by the user
// unless it is guaranteed to be immutable - terms could then be mutated

public abstract class Term {
    
    // Published interface 
    // Term subclasses are not published, with the exception of Var
    
    /** 
    * @publish
    * Returns a term representing Top/Verum.
    */
    public static Term mkTop() {
        return new Top();
    }
    
    /**
    * @publish
    * Returns a term representing Bottom/Falsum.
    */
    public static Term mkBottom() {
        return new Bottom();
    }
    
    /**
    * @publish
    * Returns a term representing the variable (or constant, depending on the
    * context in which it is used) with the given name.
    */
    public static Var mkVar(String name) {
        return new Var(name);
    }
    
    /**
    * @publish
    * Returns a term representing the conjunction of the given terms. One or
    * more terms must be provided. If only one term t is provided, the return
    * value will be exactly t.
    */
    public static Term mkAnd(Term... args) {
        Errors.precondition(args.length > 0, "One or more arguments must be given");
        if(args.length == 1) {
            return args[0];
        }
        return new AndList(ImmutableWrapperList.copyArray(args));
    }
    /**
    * @publish
    * Returns a term representing the conjunction of the given terms. One or
    * more terms must be provided. If only one term t is provided, the return
    * value will be exactly t.
    */
    public static Term mkAnd(List<Term> args) {
        Errors.precondition(args.size() > 0, "One or more arguments must be given");
        if(args.size() == 1) {
            return args.get(0);
        } 
        return new AndList(ImmutableWrapperList.copyCollection(args));
    }
    
    /**
    * @publish
    * Returns a term representing the disjunction of the given terms. One or
    * more terms must be provided. If only one term t is provided, the return
    * value will be exactly t.
    */
    public static Term mkOr(Term... args) {
        Errors.precondition(args.length > 0, "One or more arguments must be given");
        if(args.length == 1) {
            return args[0];
        }
        return new OrList(ImmutableWrapperList.copyArray(args));
    }
    /**
    * @publish
    * Returns a term representing the conjunction of the given terms. One or
    * more terms must be provided. If only one term t is provided, the return
    * value will be exactly t.
    */
    public static Term mkOr(List<Term> args) {
        Errors.precondition(args.size() > 0, "One or more arguments must be given");
        if(args.size() == 1) {
            return args.get(0);
        }
        return new OrList(ImmutableWrapperList.copyCollection(args));
    }
    
    /**
    * @publish
    * Returns a term representing the negation of the given term.
    */
    public static Term mkNot(Term t) {
        return new Not(t);
    }
    
    /**
    * @publish
    * Returns a term representing the implication "t1 implies t2".
    */
    public static Term mkImp(Term t1, Term t2) {
        return new Implication(t1, t2);
    }
    
    /**
    * @publish
    * Returns a term representing the truth value of whether t1 and t2 are equal.
    * Users should also use this for the bi-equivalence "t1 iff t2".
    */
    public static Term mkEq(Term t1, Term t2) {
        return new Eq(t1, t2);
    }
    
    /**
    * @publish
    * Returns a term representing the constraint that the given terms have
    * distinct values. Two or more terms must be provided
    */
    public static Term mkDistinct(List<? extends Term> arguments) {
        Errors.precondition(arguments.size() >= 2, "Two or more arguments must be given");
        return new Distinct(ImmutableWrapperList.copyCollection(arguments));
    }
    /**
    * @publish
    * Returns a term representing the constraint that the given terms have
    * distinct values. Two or more terms must be provided.
    */
    public static Term mkDistinct(Term... arguments) {
        Errors.precondition(arguments.length >= 2, "Two or more arguments must be given");
        return new Distinct(ImmutableWrapperList.copyArray(arguments));
    }
    
    /**
    * @publish
    * Returns a term representing the result of the application of a function with
    * the given functionName to the given arguments. At least one or more arguments
    * must be provided.
    */
    public static Term mkApp(String functionName, Term... arguments) {
        return new App(functionName, ImmutableWrapperList.copyArray(arguments));
    }
    /**
    * @publish
    * Returns a term representing the result of the application of a function with
    * the given functionName to the given arguments. At least one or more arguments
    * must be provided.
    */
    public static Term mkApp(String functionName, List<? extends Term> arguments) {
        return new App(functionName, ImmutableWrapperList.copyCollection(arguments));
    }
    
    /**
    * @publish
    * Returns a term representing the universal quantification of the given body
    * over the given annotated variables.
    * At least one or more variables must be provided.
    */
    public static Term mkForall(List<AnnotatedVar> vars, Term body) {
        ImmutableList<AnnotatedVar> varsCopy = ImmutableWrapperList.copyCollection(vars);
        return new Forall(varsCopy, body);
    }
    /**
    * @publish
    * Returns a term representing the universal quantification of the given body
    * over the given annotated variable.
    */
    public static Term mkForall(AnnotatedVar x, Term body) {
        ImmutableList<AnnotatedVar> vars = ImmutableList.of(x);
        return new Forall(vars, body);
    }
    
    /**
    * @publish
    * Returns a term representing the existential quantification of the given body
    * over the given annotated variables.
    * At least one or more variables must be provided.
    */
    public static Term mkExists(List<AnnotatedVar> vars, Term body) {
        ImmutableList<AnnotatedVar> varsCopy = ImmutableWrapperList.copyCollection(vars);
        return new Exists(varsCopy, body);
    }
    /**
    * @publish
    * Returns a term representing the existential quantification of the given body
    * over the given annotated variable.
    */
    public static Term mkExists(AnnotatedVar x, Term body) {
        ImmutableList<AnnotatedVar> vars = ImmutableList.of(x);
        return new Exists(vars, body);
    }
    
    // End of Published Interface
    
    /**
    * Returns a term representing the bi-equivalence "t1 iff t2".
    */
    public static Term mkIff(Term t1, Term t2) {
        return new Iff(t1, t2);
    }
    
    /**
    * Internal method to make AndLists without needing to copy the argument list.
    */
    public static Term mkAndF(ImmutableList<Term> arguments) {
        Errors.precondition(arguments.size() > 0, "One or more arguments must be given");
        if(arguments.size() == 1) {
            return arguments.get(0);
        }
        return new AndList(arguments);
    }
    
    /**
    * Internal method to make OrLists without needing to copy the argument list.
    */
    public static Term mkOrF(ImmutableList<Term> arguments) {
        Errors.precondition(arguments.size() > 0, "One or more arguments must be given");
        if(arguments.size() == 1) {
            return arguments.get(0);
        }
        return new OrList(arguments);
    }
    
    /**
    * Internal method to make Distinct terms without needing to copy the argument list.
    */
    public static Term mkDistinctF(ImmutableList<Term> arguments) {
        Errors.precondition(arguments.size() >= 2);
        return new Distinct(arguments);
    }
    
    /**
    * Internal method to make Apps without needing to copy the argument list.
    */
    public static Term mkAppF(String functionName, ImmutableList<Term> arguments) {
        return new App(functionName, arguments);
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
    
    /** Returns the set of Vars that appear unquantified in this term.
    * This only looks at syntax without respect to a given signature,
    * so it could also include what are intended to be constants.
    */ 
    public Set<Var> freeVarConstSymbols() {
        return new FreeVariablesVisitor().visit(this);
    }
    
    /** Returns the set of free variables of this term with respect
    * to the given signature. Constants of the signature are not included.
    */ 
    public Set<Var> freeVars(Signature signature) {
        Set<Var> freeVars = freeVarConstSymbols();
        Set<Var> constants = signature.getConstants().stream().map((AnnotatedVar av) -> av.getVar())
            .collect(Collectors.toSet());
        freeVars.removeAll(constants);
        return freeVars;
    }
    
    /**
    * Given a signature, typechecks the term with respect to the signature.
    * Returns a TypeCheckResult containing the type of the term, AND a new term
    * that is equal to the old term but with instances of Eq replaced with Iff
    * when comparing Bool types. Such a term is called "sanitized".
    */
    public TypeCheckResult typeCheck(Signature signature) {
        return TypeChecker.typeCheck(signature, this);
    }
    
    /**
    * Returns the negation normal form version of this term.
    * The term must be sanitized to call this method.
    */
    public Term nnf(Signature sig) {
        NnfVisitor nnf = new NnfVisitor(sig); 
        return nnf.visit(this);
    }
    
    /**
    * Returns an SExpr representing this term as it would appear in SMT-LIB.
    */
    public SExpr toSmtExpr() {
        return new SmtExprVisitor().visit(this);
    }
    
    /**
    * Returns a term that is alpha-equivalent to this one but whose quantified
    * variables are instead De Bruijn indices. Note that these indices are prefixed
    * by an underscore to make it clearer (e.g. the first quantified variable is "_1")
    */
    public Term deBruijn() {
        return new DeBruijnConverter().convert(this);
    }
    
    /**
    * Returns true iff the other term is alpha-equivalen to this term.
    */
    public boolean alphaEquivalent(Term other) {
        return this.deBruijn().equals(other.deBruijn());
    }
    
    public Term substitute(Var toSub, Term subWith, Set<String> forbiddenNames) {
        return new Substituter(this, toSub, subWith, forbiddenNames).substitute();
    }
    
    public Term substitute(Var toSub, Term subWith, NameGenerator nameGenerator) {
        return new Substituter(this, toSub, subWith, nameGenerator).substitute();
    }
    
    public Term substitute(Var toSub, Term subWith) {
        return substitute(toSub, subWith, Set.of());
    }
    
    public Term univInstantiate(Map<Type, List<Var>> typeInstantiations) {
        return new UnivInstantiationVisitor(typeInstantiations).visit(this);
    }
    
    public Term simplify() {
        return new SimplifyVisitor().visit(this);
    }
    
    /**
    * Returns the set of all symbol names used in the term, including:
    * free variables and constants, bound variables (even those that aren't used),
    * function names, and type names that appear on variable bindings.
    */
    public Set<String> allSymbols() {
        return new AllSymbolsVisitor().visit(this);
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
