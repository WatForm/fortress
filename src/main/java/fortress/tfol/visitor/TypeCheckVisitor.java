package fortress.tfol.visitor;

import fortress.data.Either;
import java.util.Optional;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.Set;
import java.util.HashSet;
import fortress.tfol.*;
import java.util.Iterator;

public class TypeCheckVisitor implements TermVisitor<Either<String, Type>> {
    
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
    public Either<String, Type> visitTop(Top term) {
        return Either.rightOf(Type.Bool);
    }
    
    @Override
    public Either<String, Type> visitBottom(Bottom term) {
        return Either.rightOf(Type.Bool);
    }
    
    @Override
    public Either<String, Type> visitVar(Var variable) {
        // Check variable is not an already declared function symbol
        // This must be done even with a consistent signature
        // TODO: this behaviour should be documented
        // TODO: is this considered poorly typed or a different kind of error?
        if(signature.lookupFunctionDeclaration(variable.getName()).isPresent()) {
            return Either.leftOf("Variable name " + variable.getName() + " conflicts with existing function symbol");
        }
        
        
        // Check if it is in the Context
        // Note that the context is used as a stack, so we just need to iterate
        // from front to back and not have to worry about shadowed variables.
        // e.g. in (forall v: A, forall v : B, p(v)), the context will look like
        // List[v: B, v: A], and the term will fail to typecheck if p : A -> Bool
        // since the use of v will have type B
        for(AnnotatedVar v : contextStack) {
            if(v.getName().equals(variable.getName())) {
                return Either.rightOf(v.getType());
            }
        }
        
        // If it is not in the stack, check if is in the declared constants
        return signature.lookupConstant(variable)
            .map( (AnnotatedVar av) -> Either.<String, Type>rightOf(av.getType()))
            .orElse(Either.<String, Type>leftOf("Could not determine type of variable " + variable.getName()));
    }
    
    @Override
    public Either<String, Type> visitNot(Not term) {
        return visit(term.getBody()).match(
            (String err) -> Either.leftOf(err),
            (Type t) -> {
                if(t.equals(Type.Bool)) {
                    return Either.rightOf(Type.Bool);
                } else {
                    return Either.leftOf("Argument of negation is of type " + t.getName() + " in " + term.toString());
                }
            }
        );
    }
    
    private Either<String, Type> checkBoolList(List<Term> terms, Term base) {
        for(Term term : terms) {
            Either<String, Type> result = visit(term);
            if(result.isLeft()) {
                return result;
            } else {
                Type t = result.getRight();
                if(!t.equals(Type.Bool)) {
                    return Either.leftOf("Expected type Bool but was " + t.getName() + " in " + base.toString());
                }
            }
        }
        return Either.rightOf(Type.Bool);
    }

    @Override
    public Either<String, Type> visitAndList(AndList andList) {
        return checkBoolList(andList.getArguments(), andList);
    }
    
    @Override
    public Either<String, Type> visitOrList(OrList orList) {
        return checkBoolList(orList.getArguments(), orList);
    }
    
    private Either<String, Type> sameTypeThenBool(List<Term> terms, Term base) {
        Set<Type> foundTypes = new HashSet();
        
        for(Term arg : terms) {
            Either<String, Type> result = visit(arg);
            if(result.isLeft()) {
                return result;
            } else {
                Type t = result.getRight();
                foundTypes.add(t);
            }
        }
        
        if(foundTypes.size() > 1) {
            return Either.leftOf("Arguments of multiple types " + foundTypes.toString() + " in " + base.toString());
        }
        
        return Either.rightOf(Type.Bool);
    }
    
    @Override
    public Either<String, Type> visitDistinct(Distinct term) {
        return sameTypeThenBool(term.getArguments(), term);
    }
    
    @Override
    public Either<String, Type> visitImplication(Implication term) {
        return checkBoolList(List.of(term.getLeft(), term.getRight()), term);
    }
    
    @Override
    public Either<String, Type> visitEq(Eq term) {
        return sameTypeThenBool(List.of(term.getLeft(), term.getRight()), term);
    }
    
    private Either<String, Type> checkFunction(FuncDecl funcDecl, List<Term> arguments) {
        if(funcDecl.getArity() != arguments.size()) {
            return Either.leftOf("Application of " + funcDecl.getName() + " to wrong number of arguments");
        }
        
        Iterator<Type> itTypes = funcDecl.getArgTypes().iterator();
        Iterator<Term> itArgs = arguments.iterator();
        int argNum = 0;
        while(itTypes.hasNext() && itArgs.hasNext()) {
            argNum++;
            Type expected = itTypes.next();
            Term term = itArgs.next();
            Either<String, Type> result = visit(term);
            if(result.isLeft()) {
                return result;
            } else {
                Type actual = result.getRight();
                if(!expected.equals(actual)) {
                    return Either.leftOf("In argument " + argNum + " of " + funcDecl.getName() + ", expected " + expected.getName() + " but was " + actual.getName());
                }
            }
        }
        
        return Either.rightOf(funcDecl.getResultType());
    }
    
    @Override
    public Either<String, Type> visitApp(App app) {
        String funcName = app.getFunctionName();
        List<Term> arguments = app.getArguments();
        
        return signature.lookupFunctionDeclaration(funcName) // Check for function symbol in declared functions
            .map((FuncDecl fdecl) -> checkFunction(fdecl, arguments)) // Check argument types match function declaration and return result type if true
            .orElse(Either.leftOf("Unknown function " + funcName)); // If function declaration not present
    }
    
    private Either<String, Type> visitQuantifier(Quantifier term) {
        List<AnnotatedVar> variables = term.getVars();
        
        // Must put variables on context stack in this order
        // e.g. (forall v: A v: B, p(v)), the context should be
        // List[v: B, v: A]
        for(AnnotatedVar av : variables) {
            contextStack.addFirst(av);
        }
        Either<String, Type> result = checkBoolList(List.of(term.getBody()), term);
        
        // Pop context stack
        for(AnnotatedVar av : variables) {
            contextStack.removeFirst();
        }
        return result;
    }
    
    @Override
    public Either<String, Type> visitExists(Exists term) {
        return visitQuantifier(term);
    }
    
    @Override
    public Either<String, Type> visitForall(Forall term) {
        return visitQuantifier(term);
    }
    
}
