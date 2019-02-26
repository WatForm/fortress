package fortress.tfol.visitor;

import java.util.Optional;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.Set;
import fortress.tfol.*;

public class TypeCheckVisitor implements TermVisitor<Optional<Type>> {
    
    private final Signature signature;
    private final LinkedList<AnnotatedVar> contextStack;
    
    public TypeCheckVisitor(Signature signature) {
        this.signature = signature;
        this.contextStack = new LinkedList<>();
    }
    
    // For entering partway through a term traversal
    public TypeCheckVisitor(Signature signature, LinkedList<AnnotatedVar> contextStack) {
        this.signature = signature;
        this.contextStack = contextStack;
    }
    
    @Override
    public Optional<Type> visitTop(Top term) {
        return Optional.of(Type.Bool);
    }
    
    @Override
    public Optional<Type> visitBottom(Bottom term) {
        return Optional.of(Type.Bool);
    }
    
    @Override
    public Optional<Type> visitVar(Var variable) {
        // Check variable is not an already declared function symbol
        // This must be done even with a consistent signature
        // TODO: this behaviour should be documented
        // TODO: is this considered poorly typed or a different kind of error?
        if(signature.lookupFunctionDeclaration(variable.getName()).isPresent()) {
            return Optional.empty();
        }
        
        
        // Check if it is in the Context
        // Note that the context is used as a stack, so we just need to iterate
        // from front to back and not have to worry about shadowed variables.
        // e.g. in (forall v: A, forall v : B, p(v)), the context will look like
        // List[v: B, v: A], and the term will fail to typecheck if p : A -> Bool
        // since the use of v will have type B
        for(AnnotatedVar v : contextStack) {
            if(v.getName().equals(variable.getName())) {
                return Optional.of(v.getType());
            }
        }
        
        // If it is not in the stack, check if is in the declared constants
        return signature.lookupConstant(variable)
            .map( (AnnotatedVar av) -> av.getType());
    }
    
    @Override
    public Optional<Type> visitNot(Not term) {
        if(typesAsBool(term.getBody())) {
            return Optional.of(Type.Bool);
        } else {
            return Optional.empty();
        }
    }
    
    private boolean typesAsBool(Term term) {
        return visit(term).filter(Type.Bool::equals).isPresent();
    }
    
    private boolean allTypeAsBool(List<Term> terms) {
        return terms.stream().allMatch(term -> typesAsBool(term));
    }
    
    // If the given list of terms all typecheck as bool
    private Optional<Type> checkBoolList(List<Term> terms) {
        if(allTypeAsBool(terms)) {
            return Optional.of(Type.Bool);
        } else {
            return Optional.empty();
        }
    }
    
    @Override
    public Optional<Type> visitAndList(AndList andList) {
        return checkBoolList(andList.getArguments());
    }
    
    @Override
    public Optional<Type> visitOrList(OrList orList) {
        return checkBoolList(orList.getArguments());
    }
    
    @Override
    public Optional<Type> visitDistinct(Distinct term) {
        List<Term> arguments = term.getArguments();
        List<Optional<Type>> types = arguments.stream().map(v -> visit(v)).collect(Collectors.toList());
        boolean allSameType = types.stream().allMatch(types.get(0)::equals);
        // Check first one is well typed and they all have the same type
        if(allSameType && types.get(0).isPresent()) {
            return Optional.of(Type.Bool);
        } else {
            return Optional.empty();
        }
    }
    
    @Override
    public Optional<Type> visitImplication(Implication term) {
        return checkBoolList(List.of(term.getLeft(), term.getRight()));
    }
    
    @Override
    public Optional<Type> visitEq(Eq term) {
        if(visit(term.getLeft()).equals(visit(term.getRight()))) {
            return Optional.of(Type.Bool);
        } else {
            return Optional.empty();
        }
    }
    
    private boolean functionTypeMatches(FuncDecl funcDecl, List<Term> arguments) {
        List<Optional<Type>> expected = funcDecl.getArgTypes().stream().map(
            type -> Optional.of(type)
        ).collect(Collectors.toList());
        
        List<Optional<Type>> actual = arguments.stream().map(
            term -> visit(term)
        ).collect(Collectors.toList());
        
        return expected.equals(actual);
    }
    
    @Override
    public Optional<Type> visitApp(App app) {
        String funcName = app.getFunctionName();
        List<Term> arguments = app.getArguments();
        
        return signature.lookupFunctionDeclaration(funcName) // Check for function symbol in declared functions
            .filter(fdecl -> functionTypeMatches(fdecl, arguments)) // Check argument types match function declaration
            .map(fdecl -> fdecl.getResultType()); // If true, the application's type is the declaration's result type
    }
    
    Optional<Type> visitQuantifier(Quantifier term) {
        List<AnnotatedVar> variables = term.getVars();
        
        // Must put variables on context stack in this order
        // e.g. (forall v: A v: B, p(v)), the context should be
        // List[v: B, v: A]
        for(AnnotatedVar av : variables) {
            contextStack.addFirst(av);
        }
        boolean correct = typesAsBool(term.getBody());
        
        // Pop context stack
        for(AnnotatedVar av : variables) {
            contextStack.removeFirst();
        }
        if(correct) {
            return Optional.of(Type.Bool);
        } else {
            return Optional.empty();
        }
    }
    
    @Override
    public Optional<Type> visitExists(Exists term) {
        return visitQuantifier(term);
    }
    
    @Override
    public Optional<Type> visitForall(Forall term) {
        return visitQuantifier(term);
    }
    
}
