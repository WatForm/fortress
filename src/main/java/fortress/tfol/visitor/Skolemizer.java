package fortress.tfol.visitor;

import fortress.tfol.*;
import fortress.data.NameGenerator;

import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.LinkedHashMap;

// Skolemizes a given term
// Free variables in the given term are ignored, so the top level term must be
// closed with respect to the signature in question for this operation to be valid.
public abstract class Skolemizer implements TermVisitor<Term> {
    private Term toplevelTerm;
    private NameGenerator gen;
    
    private LinkedHashMap<Var, Type> accUnivQuantVars;
    private Map<Var, Term> accSkolemSubstitutions;
    
    public Skolemizer(Term toplevelTerm, NameGenerator gen) {
        this.toplevelTerm = toplevelTerm;
        this.gen = gen;
    }
    
    Term convert() {
        return visit(toplevelTerm);
    }
    
    
    @Override
    public Term visitTop(Top term) {
        return term;
    }
    
    @Override
    public Term visitBottom(Bottom term) {
        return term;
    }
    
    // @Override
    // public Term visitVar(Var term);
    
    @Override
    public Term visitNot(Not term) {
        return term;
    }
    
    @Override
    public Term visitAndList(AndList term) {
        return term;
    }
    // public Term visitOrList(OrList term);
    // public Term visitDistinct(Distinct term);
    // public Term visitIff(Iff term);
    // public Term visitImplication(Implication term);
    // public Term visitEq(Eq term);
    // public Term visitApp(App term);
    // public Term visitExists(Exists term);
    // public Term visitForall(Forall term);
}
