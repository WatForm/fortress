package fortress.tfol.operations;

import fortress.tfol.*;
import java.util.Set;
import java.util.HashSet;
import java.util.List;
import java.util.ArrayList;

// Returns all variables, both bound and unbound, used in a term
// Note: Bound variables that are not used are still returned
public class AllVariablesVisitor implements TermVisitor<Set<Var>> {
    
    @Override
    public Set<Var> visitTop(Top term) {
        return new HashSet<Var>();
    }
    
    @Override
    public Set<Var> visitBottom(Bottom term) {
        return new HashSet<Var>();
    }
    
    @Override
    public Set<Var> visitVar(Var var) {
        HashSet<Var> set = new HashSet<>();
        set.add(var);
        return set;
    }
    
    @Override
    public Set<Var> visitNot(Not term) {
        return visit(term.getBody());
    }
    
    private Set<Var> combineVarsOfList(List<? extends Term> terms) {
        Set<Var> vars = new HashSet<>();
        terms.stream().map(this::visit).forEach(
            set -> vars.addAll(set)
        );
        return vars;
    }
    
    @Override
    public Set<Var> visitAndList(AndList andList) {
        return combineVarsOfList(andList.getArguments());
    }
    
    @Override
    public Set<Var> visitOrList(OrList orList) {
        return combineVarsOfList(orList.getArguments());
    }
    
    @Override
    public Set<Var> visitDistinct(Distinct term) {
        return combineVarsOfList(term.getArguments());
    }
    
    @Override
    public Set<Var> visitImplication(Implication term) {
        return combineVarsOfList(List.of(term.getLeft(), term.getRight()));
    }
    
    @Override
    public Set<Var> visitIff(Iff iff) {
        return combineVarsOfList(List.of(iff.getLeft(), iff.getRight()));
    }
    
    @Override
    public Set<Var> visitEq(Eq term) {
        return combineVarsOfList(List.of(term.getLeft(), term.getRight()));
    }
    
    @Override
    public Set<Var> visitApp(App term) {
        return combineVarsOfList(term.getArguments());
    }
    
    private Set<Var> visitQuantifier(Quantifier term) {
        Set<Var> vars = visit(term.getBody());
        for(AnnotatedVar av : term.getVars()) {
            vars.add(av.getVar());
        }
        return vars;
    }
    
    @Override
    public Set<Var> visitExists(Exists term) {
        return visitQuantifier(term);
    }
    
    @Override
    public Set<Var> visitForall(Forall term) {
        return visitQuantifier(term);
    }
    
}
