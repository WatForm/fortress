package fortress.tfol.operations;

import fortress.tfol.*;

import java.util.LinkedList;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;

public class DeBruijnConverter {
    private int counter;
    private LinkedList<Mapping> mappingStack;
    private DeBruijnVisitor visitor;
    
    private class Mapping {
        private int index;
        private Var variable;
        
        public Mapping(int index, Var variable) {
            this.index = index;
            this.variable = variable;
        }
    }
    
    public DeBruijnConverter() {
        this.counter = 0;
        this.mappingStack = new LinkedList<>();
        this.visitor = new DeBruijnVisitor();
    }
    
    public Term convert(Term term) {
        this.counter = 0;
        this.mappingStack = new LinkedList<>();
        return visitor.visit(term);
    }
    
    private class DeBruijnVisitor implements TermVisitor<Term> {
        
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
            for(Mapping m : mappingStack) {
                if(var.equals(m.variable)) {
                    return Term.mkVar("_" + Integer.toString(m.index));
                }
            }
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
            return eq.mapArguments(this::visit);
        }
        
        @Override
        public Term visitApp(App app) {
            return app.mapArguments(this::visit);
        }
        
        private void pushVar(AnnotatedVar av) {
            counter++;
            Mapping m = new Mapping(counter, av.getVar());
            mappingStack.addFirst(m);
        }
        
        private void popVar() {
            counter--;
            mappingStack.removeFirst();
        }
        
        @Override
        public Term visitExists(Exists exists) {
            List<AnnotatedVar> newVars = new ArrayList<>();
            for(AnnotatedVar av : exists.getVars()) {
                pushVar(av);
                newVars.add(Term.mkVar("_" + Integer.toString(counter)).of(av.getType()));
            }
            
            Term body = visit(exists.getBody());
            
            // Return state back to way it was
            for(AnnotatedVar av : exists.getVars()) {
                popVar();
            }
            
            return Term.mkExists(newVars, body);
        }
        
        @Override
        public Term visitForall(Forall forall) {
            List<AnnotatedVar> newVars = new ArrayList<>();
            for(AnnotatedVar av : forall.getVars()) {
                pushVar(av);
                newVars.add(Term.mkVar("_" + Integer.toString(counter)).of(av.getType()));
            }
            
            Term body = visit(forall.getBody());
            
            // Return state back to way it was
            for(AnnotatedVar av : forall.getVars()) {
                popVar();
            }
            
            return Term.mkForall(newVars, body);
        }
    }
    
}
