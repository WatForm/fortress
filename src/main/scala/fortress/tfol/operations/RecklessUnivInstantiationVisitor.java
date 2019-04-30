package fortress.tfol.operations;

import java.util.Map;
import java.util.HashMap;
import java.lang.IllegalArgumentException;
import java.util.List;
import java.util.ArrayList;
import fortress.tfol.*;
import fortress.data.CartesianProduct;
import fortress.util.Errors;

// TODO this could be made much more efficient

public class RecklessUnivInstantiationVisitor implements TermVisitor<Term> {
    private Map<Type, List<Term>> typeInstantiations;
    
    public RecklessUnivInstantiationVisitor(Map<Type, List<Term>> typeInstantiations) {
        this.typeInstantiations = typeInstantiations;
    }
    
    @Override
    public Term visitTop() {
        return Term.mkTop();
    }
    
    @Override
    public Term visitBottom() {
        return Term.mkBottom();
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
        
        // TODO does the order of quantifier instantiation matter? Here we do a bottom up approach
        Term body = visit(forall.getBody());
        
        List<Term> toConjunct = new ArrayList<>();
        
        // Forall x_1: A_1, x_2 : A_2, ... x_n: A_n
        // Where A_i is to be instantiated using the set S_i
        // Get the list [S_1, S_2, ..., S_n]
        // and the list [x_1, x_2, ..., x_n]
        List<List<Term>> listOfTypeSets = new ArrayList<>();
        List<Var> vars = new ArrayList<>();
        for(AnnotatedVar av: forall.getVars()) {
            Type type = av.getType();
            listOfTypeSets.add(typeInstantiations.get(type));
            vars.add(av.getVar());
        }
        
        CartesianProduct<Term> cartesianProduct = new CartesianProduct<>(listOfTypeSets);
        for(List<Term> substitution : cartesianProduct) {
            Errors.verify(substitution.size() == vars.size());
            
            Map<Var, Term> varSubstitutions = new HashMap<>();
            for(int i = 0; i < vars.size(); i++) {
                varSubstitutions.put(vars.get(i), substitution.get(i));
            }
            
            // NOTE because we are substituting with fresh variables, there
            // should never be any variable capture or any other name issues
            Term bodyInstance = body.recklessSubstituteJava(varSubstitutions);
            toConjunct.add(bodyInstance);
        }
        return Term.mkAnd(toConjunct);
    }
    
    @Override
    public Term visitDomainElement(DomainElement d) {
        return fortress.util.Errors.<Term>notImplemented();
    }
    
    @Override
    public Term visitTC(TC tc) {
        throw new IllegalArgumentException("Term must not have TC: " + tc.toString());
    }
    
    @Override
    public Term visitIntegerLiteral(IntegerLiteral literal) {
        return fortress.util.Errors.<Term>notImplemented();
    }
    
    @Override
    public Term visitBitVectorLiteral(BitVectorLiteral literal) {
        return fortress.util.Errors.<Term>notImplemented();
    }
    
    @Override
    public Term visitEnumValue(EnumValue e) {
        return fortress.util.Errors.<Term>notImplemented();
    }
}
