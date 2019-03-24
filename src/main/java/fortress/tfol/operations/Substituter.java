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

public class Substituter {
    private Term topLevelTerm;
    private NameGenerator nameGen;
    private Var toSub;
    private Term subWith;
    private Set<Var> freeVarsOfSubWith;
    private SubstitutionVisitor visitor;
    
    /**
    * Creates a Substituter that is primed to perform the substitution
    * [toSub \u21A6 subWith] inside the topLevelTerm.
    * The substituter will perform alpha-renaming to avoid variable capture when
    * necessary.
    * When creating new variables for alpha-renaming, it will not use any of
    * the names given in forbiddenNames;
    */
    public Substituter(Term topLevelTerm, Var toSub, Term subWith, Set<String> forbiddenNames) {
        this.topLevelTerm = topLevelTerm;
        this.toSub = toSub;
        this.subWith = subWith;
        this.freeVarsOfSubWith = subWith.freeVarConstSymbols();
        // Copy things so we don't modify them
        Set<String> forbidden = new HashSet(forbiddenNames);
        
        // Forbid all names used in term
        forbidden.addAll(topLevelTerm.allSymbols());
        
        this.nameGen = new SubIntNameGenerator(forbidden, 0);
        this.visitor = new SubstitutionVisitor();
    }
    
    /**
    * Creates a Substituter that is primed to perform the substitution
    * [toSub \u21A6] subWith inside the topLevelTerm.
    * The substituter will perform alpha-renaming to avoid variable capture when
    * necessary.
    * When creating new variables for alpha-renaming, it will use the given name
    * generator.
    * This for example can be used to make sure when introducing new variables
    * that the substituter avoids a certain set of symbols (e.g. function names
    * that are used in some signature).
    * Note that this will mutate the name generator object.
    * The substituter may also forbid other names inside the name generator
    * to help avoid variable capture.
    */
    public Substituter(Term topLevelTerm, Var toSub, Term subWith, NameGenerator nameGen) {
        // Copy things so we don't modify them
        this.topLevelTerm = topLevelTerm;
        this.toSub = toSub;
        this.subWith = subWith;
        this.freeVarsOfSubWith = subWith.freeVarConstSymbols();
        this.nameGen = nameGen;
        this.visitor = new SubstitutionVisitor();
        
        // Forbid all names used in term
        for(String name : topLevelTerm.allSymbols()) {
            this.nameGen.forbidName(name);
        }
    }
    
    /**
    * Perform the substitution (which will mutate the name generator if one
    * was provided) and return the resulting term.
    * This method should not be called more than once for a given Substituter object.
    */
    public Term substitute() {
        return visitor.visit(topLevelTerm);
    }
    
    private class SubstitutionVisitor implements TermVisitor<Term> {
        
        // Note that this is an "inner" (non-static nested) class that still
        // has access to the enclosing class instance variables.
        
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
            if(var.equals(toSub)) {
                return subWith;
            } else {
                return var;
            }
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
        
        @Override
        public Term visitExists(Exists exists) {
            // Substitute x->t in (exists x . phi) equals (exists x . phi)
            for(AnnotatedVar av : exists.getVars()) {
                if(av.getVar().equals(toSub)) {
                    return exists;
                }
            }
            
            // Avoid variable capturing
            List<AnnotatedVar> newVars = new ArrayList<>();
            Term newBody = exists.getBody();
            for(AnnotatedVar av : exists.getVars()) {
                Var v = av.getVar();
                if(freeVarsOfSubWith.contains(v)) {
                    AnnotatedVar replacement = Term.mkVar(nameGen.freshName(v.getName())).of(av.getType());
                    newBody = new Substituter(newBody, v, replacement.getVar(), nameGen).substitute();
                    newVars.add(replacement);
                } else {
                    newVars.add(av);
                }
            }
            Term finalBody = visit(newBody);
            
            return Term.mkExists(newVars, finalBody);
        }
        
        @Override
        public Term visitForall(Forall forall){
            // Substitute x->t in (forall x . phi) equals (forall x . phi)
            for(AnnotatedVar av : forall.getVars()) {
                if(av.getVar().equals(toSub)) {
                    return forall;
                }
            }
            
            // Avoid variable capturing
            List<AnnotatedVar> newVars = new ArrayList<>();
            Term newBody = forall.getBody();
            for(AnnotatedVar av : forall.getVars()) {
                Var v = av.getVar();
                if(freeVarsOfSubWith.contains(v)) {
                    AnnotatedVar replacement = Term.mkVar(nameGen.freshName(v.getName())).of(av.getType());
                    newBody = new Substituter(newBody, v, replacement.getVar(), nameGen).substitute();
                    newVars.add(replacement);
                } else {
                    newVars.add(av);
                }
            }
            Term finalBody = visit(newBody);
            
            return Term.mkForall(newVars, finalBody);
        }
    }
    
}
