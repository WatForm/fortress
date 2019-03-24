package fortress.tfol.operations;

import java.util.Map;
import java.lang.IllegalArgumentException;
import java.util.List;
import java.util.ArrayList;
import fortress.tfol.*;
import fortress.data.CartesianProduct;
import fortress.util.Errors;

// TODO this could be made much more efficient

public class UnivInstantiationVisitor implements TermVisitor<Term> {
    private Map<Type, List<Var>> typeInstantiations;
    
    public UnivInstantiationVisitor(Map<Type, List<Var>> typeInstantiations) {
        this.typeInstantiations = typeInstantiations;
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
        return var;
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
        // Eq is atomic
        return eq;
    }
    
    @Override
    public Term visitApp(App app) {
        // App is atomic
        return app;
    }
    
    @Override
    public Term visitExists(Exists exists) {
        // Should not exist
        throw new IllegalArgumentException("Term must be existential-quantifier-free");
    }
    
    @Override
    public Term visitForall(Forall forall) {
        // TODO this assumes each type is instantiated, which we may change later
        // Perhaps it makes more sense to do each single type instantation one at a time?
        // Or would that take too long?
        
        // TODO does the order of quantifier instantiation matter? Here we do a bottom up approach
        Term body = visit(forall.getBody());
        
        List<Term> toConjunct = new ArrayList<>();
        
        // Forall x_1: A_1, x_2 : A_2, ... x_n: A_n
        // Where A_i is to be instantiated using the set S_i
        // Get the list [S_1, S_2, ..., S_n]
        // and the list [x_1, x_2, ..., x_n]
        List<List<Var>> listOfTypeSets = new ArrayList<>();
        List<Var> vars = new ArrayList<>();
        for(AnnotatedVar av: forall.getVars()) {
            Type type = av.getType();
            listOfTypeSets.add(typeInstantiations.get(type));
            vars.add(av.getVar());
        }
        
        CartesianProduct<Var> cartesianProduct = new CartesianProduct(listOfTypeSets);
        for(List<Var> substitution : cartesianProduct) {
            Errors.failIf(substitution.size() != vars.size());
            Term bodyInstance = body;
            for(int i = 0; i < vars.size(); i++) {
                // NOTE because we are substituting with fresh variables, there
                // should never be any variable capture or any other name issues
                // TODO note that the above means this could be more efficient!
                // We could use a faster substituter that doesn't care about capture
                // TODO it would be especially much faster to do multiple substitutions at once
                bodyInstance = bodyInstance.substitute(vars.get(i), substitution.get(i));
            }
            toConjunct.add(bodyInstance);
        }
        // TODO what if size 1?
        return Term.mkAnd(toConjunct);
    }
}
