package fortress.tfol.operations;

import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import java.util.stream.Collectors;
import fortress.data.NameGenerator;
import fortress.data.SubIntNameGenerator;
import java.util.List;
import java.util.ArrayList;
import fortress.tfol.*;

public class RecklessSubstitutionVisitor implements TermVisitor<Term> {
    private Map<Var, Term> substitutions;
    
    /**
    * Creates a substituter that is primed to perform the substitutions
    * [x_1 to t_1, ..., x_n to t_n].
    * The substituter will NOT avoid variable capture; it is the responsibility
    * of the caller to make sure the substitution terms do not contain free
    * variables that will be captured.
    * If in doubt, do not use this class.
    */
    public RecklessSubstitutionVisitor(Map<Var, Term> substitutions) {
        this.substitutions = new HashMap<>(substitutions);
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
    public Term visitVar(Var var) {
        return substitutions.getOrDefault(var, var);
    }
    
    @Override
    public Term visitNot(Not not) {
        return not.mapBody(this::visit);
    }
    
    @Override
    public Term visitAndList(AndList and) {
        return and.mapArguments(this::visit);
    }
    
    @Override
    public Term visitOrList(OrList or) {
        return or.mapArguments(this::visit);
    }
    
    @Override
    public Term visitDistinct(Distinct dist) {
        return dist.mapArguments(this::visit);
    }
    
    @Override
    public Term visitImplication(Implication imp) {
        return imp.mapArguments(this::visit);
    }
    
    @Override
    public Term visitIff(Iff iff) {
        return iff.mapArguments(this::visit);
    }
    
    @Override
    public Term visitEq(Eq eq) {
        return eq.mapArguments(this::visit);
    }
    
    @Override
    public Term visitApp(App app) {
        return app.mapArguments(this::visit);
    }
    
    public Term visitQuantifier(Quantifier quant) {
        // Substitute x->t in (exists x . phi) becomes (exists x . phi)
        // Remove these (temporarily) from the substitution
        Map<Var, Term> removedSubstitutions = new HashMap<>();
        for(AnnotatedVar av : quant.getVars()) {
            Term t = substitutions.remove(av.getVar());
            if(t != null) {
                removedSubstitutions.put(av.getVar(), t);
            }
        }
        
        Term result;
        if(substitutions.size() > 0) {
            result = quant.mapBody(this::visit);
        } else {
            result = quant;
        }
        
        // Put back any substitutions removed
        substitutions.putAll(removedSubstitutions);
        
        return result;
    }
    
    @Override
    public Term visitExists(Exists exists) {
        return visitQuantifier(exists);
    }
    
    @Override
    public Term visitForall(Forall forall){
        return visitQuantifier(forall);
    }
    
}
