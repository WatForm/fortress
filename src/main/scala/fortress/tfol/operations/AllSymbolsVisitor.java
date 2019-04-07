package fortress.tfol.operations;

import fortress.tfol.*;
import java.util.Set;
import java.util.HashSet;
import java.util.List;
import java.util.ArrayList;

/**
* Visits the given term to return the set of all symbol names used in the term,
* including: free variables and constants, bound variables (even those that aren't used),
* function names, and type names that appear on variable bindings.
*/
public class AllSymbolsVisitor implements TermVisitor<Set<String>> {
    
    @Override
    public Set<String> visitTop(Top top) {
        return new HashSet<>();
    }
    
    @Override
    public Set<String> visitBottom(Bottom bottom) {
        return new HashSet<>();
    }
    
    @Override
    public Set<String> visitVar(Var var) {
        HashSet<String> set = new HashSet<>();
        set.add(var.getName());
        return set;
    }
    
    @Override
    public Set<String> visitNot(Not not) {
        return visit(not.getBody());
    }
    
    private Set<String> combineVarsOfList(List<? extends Term> terms) {
        Set<String> names = new HashSet<>();
        terms.stream().map(this::visit).forEach(
            set -> names.addAll(set)
        );
        return names;
    }
    
    @Override
    public Set<String> visitAndList(AndList andList) {
        return combineVarsOfList(andList.getArguments());
    }
    
    @Override
    public Set<String> visitOrList(OrList orList) {
        return combineVarsOfList(orList.getArguments());
    }
    
    @Override
    public Set<String> visitDistinct(Distinct term) {
        return combineVarsOfList(term.getArguments());
    }
    
    @Override
    public Set<String> visitImplication(Implication term) {
        return combineVarsOfList(List.of(term.getLeft(), term.getRight()));
    }
    
    @Override
    public Set<String> visitIff(Iff iff) {
        return combineVarsOfList(List.of(iff.getLeft(), iff.getRight()));
    }
    
    @Override
    public Set<String> visitEq(Eq term) {
        return combineVarsOfList(List.of(term.getLeft(), term.getRight()));
    }
    
    @Override
    public Set<String> visitApp(App term) {
        Set<String> names = combineVarsOfList(term.getArguments());
        names.add(term.getFunctionName());
        return names;
    }
    
    private Set<String> visitQuantifier(Quantifier term) {
        Set<String> names = visit(term.getBody());
        for(AnnotatedVar av : term.getVars()) {
            names.add(av.getVar().getName());
            names.add(av.getType().getName());
        }
        return names;
    }
    
    @Override
    public Set<String> visitExists(Exists term) {
        return visitQuantifier(term);
    }
    
    @Override
    public Set<String> visitForall(Forall term) {
        return visitQuantifier(term);
    }
    
}
