package fortress.tfol.operations;

import java.util.Set;
import java.util.HashSet;
import java.util.stream.Collectors;
import java.util.List;
import fortress.tfol.*;

// Yields a mutable set of variables containing all the Vars (which may be constants
// depending on the theory) that appears unquantified in the term
public class FreeVariablesVisitor implements TermVisitor<Set<Var>> {
    
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
    
    private Set<Var> combineFreeVarsOfList(List<? extends Term> terms) {
        Set<Var> freeVars = new HashSet<>();
        terms.stream().map(this::visit).forEach(
            set -> freeVars.addAll(set)
        );
        return freeVars;
    }
    
    @Override
    public Set<Var> visitAndList(AndList andList) {
        return combineFreeVarsOfList(andList.getArguments());
    }
    
    @Override
    public Set<Var> visitOrList(OrList orList) {
        return combineFreeVarsOfList(orList.getArguments());
    }
    
    @Override
    public Set<Var> visitDistinct(Distinct term) {
        return combineFreeVarsOfList(term.getArguments());
    }
    
    @Override
    public Set<Var> visitImplication(Implication term) {
        return combineFreeVarsOfList(List.of(term.getLeft(), term.getRight()));
    }
    
    @Override
    public Set<Var> visitIff(Iff term) {
        return combineFreeVarsOfList(List.of(term.getLeft(), term.getRight()));
    }
    
    @Override
    public Set<Var> visitEq(Eq term) {
        return combineFreeVarsOfList(List.of(term.getLeft(), term.getRight()));
    }
    
    @Override
    public Set<Var> visitApp(App term) {
        return combineFreeVarsOfList(term.getArguments());
    }
    
    private Set<Var> visitQuantifier(Quantifier term) {
        Set<Var> bodyFreeVars = visit(term.getBody());
        bodyFreeVars.removeAll(term.getVars().stream().map(av -> av.getVar()).collect(Collectors.toList()));
        return bodyFreeVars;
    }
    
    @Override
    public Set<Var> visitExists(Exists term) {
        return visitQuantifier(term);
    }
    
    @Override
    public Set<Var> visitForall(Forall term) {
        return visitQuantifier(term);
    }
    
    @Override
    public Set<Var> visitDomainElement(DomainElement d) {
        return fortress.util.Errors.<Set<Var>>notImplemented();
    }
    
    @Override
    public Set<Var> visitTC(TC tc) {
        return fortress.util.Errors.<Set<Var>>notImplemented();
    }
    
}
