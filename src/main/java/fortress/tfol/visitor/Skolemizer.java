package fortress.tfol.visitor;

import fortress.tfol.*;
import fortress.data.NameGenerator;

import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.lang.IllegalArgumentException;

// Skolemizes a given term
// Free variables in the given term are ignored, so the top level term must be
// closed with respect to the signature in question for this operation to be valid.
public abstract class Skolemizer implements TermVisitor<Term> {
    private Term toplevelTerm;
    private NameGenerator gen;
    
    public Skolemizer(Term toplevelTerm, NameGenerator gen) {
        this.toplevelTerm = toplevelTerm;
        this.gen = gen;
    }
    
    Term convert() {
        return visit(toplevelTerm);
    }
    
    @Override
    public Term visitTop(Top top) {
        return top;
    }
    
    @Override
    public Term visitBottom(Bottom bottom) {
        return bottom;
    }
    
    @Override
    public Term visitVar(Var variable) {
        return variable;
    }
    
    @Override
    public Term visitNot(Not not) {
        return Term.mkNot(visit(not.getBody()));
    }
    
    @Override
    public Term visitAndList(AndList and) {
        return and.mapArguments(this::visit);
    }
    
    // @Override
    // public Term visitOrList(OrList or) {
    //     return Term.mkOr(visit(or.getLeft()), visit(or.getRight()));
    // }
    
    @Override
    public Term visitDistinct(Distinct distinct) {
        throw new IllegalArgumentException("Term supposed to be in NNF but found distinct: " + distinct.toString());
    }
    
    @Override
    public Term visitIff(Iff iff) {
        throw new IllegalArgumentException("Term supposed to be in NNF but found iff: " + iff.toString());
    }
    
    @Override
    public Term visitImplication(Implication imp) {
        throw new IllegalArgumentException("Term supposed to be in NNF but found imp: " + imp.toString());
    }
    
    @Override
    public Term visitEq(Eq eq) {
        return Term.mkEq(visit(eq.getLeft()), visit(eq.getRight()));
    }
    // public Term visitApp(App term);
    // public Term visitExists(Exists term);
    // public Term visitForall(Forall term);
}
