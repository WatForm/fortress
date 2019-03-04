package fortress.tfol.visitor;

import fortress.tfol.*;

import java.util.LinkedList;
import java.util.stream.Collectors;
import java.util.List;
import java.util.ArrayList;

public class DeBruijnConverter implements TermVisitor<Term>{
    private int counter;
    private LinkedList<Mapping> mappingStack;
    
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
        this.mappingStack = new LinkedList();
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
        for(Mapping m : mappingStack) {
            if(var.equals(m.variable)) {
                return Term.mkVar("_" + Integer.toString(m.index));
            }
        }
        return var;
    }
    
    @Override
    public Term visitNot(Not not) {
        return visit(not);
    }
    
    @Override
    public Term visitAndList(AndList and) {
        return Term.mkAnd(
            and.getArguments().stream().map(this::visit).collect(Collectors.toList())
        );
    }
    
    @Override
    public Term visitOrList(OrList or) {
        return Term.mkOr(
            or.getArguments().stream().map(this::visit).collect(Collectors.toList())
        );
    }
    
    @Override
    public Term visitDistinct(Distinct dist) {
        return Term.mkDistinct(
            dist.getArguments().stream().map(this::visit).collect(Collectors.toList())
        );
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
        return Term.mkApp(app.getFunctionName(),
            app.getArguments().stream().map(this::visit).collect(Collectors.toList())
        );
    }
    
    @Override
    public Term visitExists(Exists exists) {
        List<AnnotatedVar> newVars = new ArrayList();
        for(AnnotatedVar av : exists.getVars()) {
            counter++;
            Mapping m = new Mapping(counter, av.getVar());
            mappingStack.addFirst(m);
            newVars.add(Term.mkVar("_" + Integer.toString(counter)).of(av.getType()));
        }
        
        Term body = visit(exists.getBody());
        
        // Return state back to way it was
        for(AnnotatedVar av : exists.getVars()) {
            counter--;
            mappingStack.removeFirst();
        }
        
        return Term.mkExists(newVars, body);
    }
    
    @Override
    public Term visitForall(Forall forall) {
        List<AnnotatedVar> newVars = new ArrayList();
        for(AnnotatedVar av : forall.getVars()) {
            counter++;
            Mapping m = new Mapping(counter, av.getVar());
            mappingStack.addFirst(m);
            newVars.add(Term.mkVar("_" + Integer.toString(counter)).of(av.getType()));
        }
        
        Term body = visit(forall.getBody());
        
        // Return state back to way it was
        for(AnnotatedVar av : forall.getVars()) {
            counter--;
            mappingStack.removeFirst();
        }
        
        return Term.mkForall(newVars, body);
    }
    
}
