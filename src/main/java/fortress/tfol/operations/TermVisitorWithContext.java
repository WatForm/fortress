package fortress.tfol.operations;

import java.util.Optional;
import java.util.Deque;
import java.util.LinkedList;
import fortress.tfol.*;

abstract class TermVisitorWithContext<T> implements TermVisitor<T> {
    protected Signature signature;
    private Deque<AnnotatedVar> typeContextStack;
    
    protected TermVisitorWithContext(Signature signature) {
        this.signature = signature;
        this.typeContextStack = new LinkedList();
    }
    
    // For entering partway through a term traversal
    protected TermVisitorWithContext(Signature signature, Deque<AnnotatedVar> typeContextStack) {
        this.signature = signature;
        this.typeContextStack = typeContextStack;
    }
    
    protected Optional<FuncDecl> lookupFunctionDeclaration(String name) {
        return signature.lookupFunctionDeclaration(name);
    }
    
    // Looks up variable type in context first, then tries constants
    protected Optional<Type> lookupType(Var variable) {
        // Check if it is in the Context
        // Note that the context is used as a stack, so we just need to iterate
        // from front to back and not have to worry about shadowed variables.
        // e.g. in (forall v: A, forall v : B, p(v)), the context will look like
        // List[v: B, v: A], and the term will fail to typecheck if p : A -> Bool
        // since the use of v will have type B
        for(AnnotatedVar av : typeContextStack) {
            if(av.getName().equals(variable.getName())) {
                return Optional.of(av.getType());
            }
        }
        
        // If it is not in the stack, check if is in the declared constants
        return signature.lookupConstant(variable)
            .map( (AnnotatedVar av) -> av.getType());
    }
    
    abstract T visitForallInner(Forall forall);
    abstract T visitExistsInner(Exists exists);
    
    @Override
    final public T visitForall(Forall forall) {
        // Must put variables on context stack in this order
        // e.g. (forall v: A v: B, p(v)), the context should be
        // List[v: B, v: A]
        for(AnnotatedVar av : forall.getVars()) {
            typeContextStack.addFirst(av);
        }
        
        T result = visitForallInner(forall);
        
        // Pop context stack
        for(AnnotatedVar av : forall.getVars()) {
            typeContextStack.removeFirst();
        }
        
        return result;
    }
    
    @Override
    final public T visitExists(Exists exists) {
        // Must put variables on context stack in this order
        // e.g. (forall v: A v: B, p(v)), the context should be
        // List[v: B, v: A]
        for(AnnotatedVar av : exists.getVars()) {
            typeContextStack.addFirst(av);
        }
        
        T result = visitExistsInner(exists);
        
        // Pop context stack
        for(AnnotatedVar av : exists.getVars()) {
            typeContextStack.removeFirst();
        }
        
        return result;
    }
}