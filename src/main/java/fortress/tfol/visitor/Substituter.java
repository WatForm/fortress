package fortress.tfol.visitor;

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
    
    public Substituter(Term topLevelTerm, Var toSub, Term subWith, Set<String> forbiddenNames) {
        this.topLevelTerm = topLevelTerm;
        this.toSub = toSub;
        this.subWith = subWith;
        this.freeVarsOfSubWith = subWith.freeVarConstSymbols();
        // Copy things so we don't modify them
        Set<String> forbidden = new HashSet(forbiddenNames);
        // Forbid all names used in term
        AllVariablesVisitor allVars = new AllVariablesVisitor();
        Set<String> usedNames = allVars.visit(topLevelTerm).stream().map(
            (Var v) -> v.getName()
        ).collect(Collectors.toSet());
        forbidden.addAll(usedNames);
        
        this.nameGen = new SubIntNameGenerator(forbidden);
        this.visitor = new SubstitutionVisitor(this);
    }
    
    public Substituter(Term topLevelTerm, Var toSub, Term subWith, NameGenerator nameGen) {
        // Copy things so we don't modify them
        this.topLevelTerm = topLevelTerm;
        this.toSub = toSub;
        this.subWith = subWith;
        this.freeVarsOfSubWith = subWith.freeVarConstSymbols();
        this.nameGen = nameGen;
        this.visitor = new SubstitutionVisitor(this);
    }
    
    public Term substitute() {
        return visitor.visit(topLevelTerm);
    }
    
    private class SubstitutionVisitor implements TermVisitor<Term> {
        private Substituter sub;
        
        public SubstitutionVisitor(Substituter sub) {
            this.sub = sub;
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
            if(var.equals(sub.toSub)) {
                return sub.subWith;
            } else {
                return var;
            }
        }
        
        @Override
        public Term visitNot(Not not) {
            return visit(not.getBody());
        }
        
        @Override
        public Term visitAndList(AndList and) {
            List<Term> args = new ArrayList();
            for(Term arg : and.getArguments()) {
                args.add(visit(arg));
            }
            return Term.mkAnd(args);
        }
        
        @Override
        public Term visitOrList(OrList or) {
            List<Term> args = new ArrayList();
            for(Term arg : or.getArguments()) {
                args.add(visit(arg));
            }
            return Term.mkOr(args);
        }
        
        @Override
        public Term visitDistinct(Distinct dist) {
            List<Term> args = new ArrayList();
            for(Term arg : dist.getArguments()) {
                args.add(visit(arg));
            }
            return Term.mkDistinct(args);
        }
        
        @Override
        public Term visitImplication(Implication imp) {
            return Term.mkImp(visit(imp.getLeft()), visit(imp.getRight()));
        }
        
        @Override
        public Term visitIff(Iff iff) {
            return Term.mkIff(visit(iff.getLeft()), visit(iff.getRight()));
        }
        
        @Override
        public Term visitEq(Eq eq) {
            return Term.mkEq(visit(eq.getLeft()), visit(eq.getRight()));
        }
        
        @Override
        public Term visitApp(App app) {
            List<Term> args = new ArrayList();
            for(Term arg : app.getArguments()) {
                args.add(visit(arg));
            }
            return Term.mkApp(app.getFunctionName(), args);
        }
        
        @Override
        public Term visitExists(Exists exists) {
            // Substitute x->t in (exists x . phi) equals (exists x . phi)
            for(AnnotatedVar av : exists.getVars()) {
                if(av.getVar().equals(sub.toSub)) {
                    return exists;
                }
            }
            
            // Avoid variable capturing
            List<AnnotatedVar> newVars = new ArrayList();
            Term newBody = exists.getBody();
            for(AnnotatedVar av : exists.getVars()) {
                Var v = av.getVar();
                if(sub.freeVarsOfSubWith.contains(v)) {
                    AnnotatedVar replacement = Term.mkVar(sub.nameGen.freshName(v.getName())).of(av.getType());
                    newBody = new Substituter(newBody, v, replacement.getVar(), sub.nameGen).substitute();
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
                if(av.getVar().equals(sub.toSub)) {
                    return forall;
                }
            }
            
            // Avoid variable capturing
            List<AnnotatedVar> newVars = new ArrayList();
            Term newBody = forall.getBody();
            for(AnnotatedVar av : forall.getVars()) {
                Var v = av.getVar();
                if(sub.freeVarsOfSubWith.contains(v)) {
                    AnnotatedVar replacement = Term.mkVar(sub.nameGen.freshName(v.getName())).of(av.getType());
                    newBody = new Substituter(newBody, v, replacement.getVar(), sub.nameGen).substitute();
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
