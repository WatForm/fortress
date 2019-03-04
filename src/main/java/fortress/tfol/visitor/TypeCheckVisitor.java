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

public class TypeCheckVisitor extends TermVisitorWithContext<Either<String, Type>> {
    
    public TypeCheckVisitor(Signature signature) {
        super(signature);
    }
    
    // For entering partway through a term traversal
    public TypeCheckVisitor(Signature signature, LinkedList<AnnotatedVar> contextStack) {
        super(signature, contextStack);
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
        if(lookupFunctionDeclaration(variable.getName()).isPresent()) {
            return Either.leftOf("Variable or constant name " + variable.getName() + " conflicts with existing function symbol");
        }
        
        return lookupType(variable)
            .map( (Type type) -> Either.<String, Type>rightOf(type) )
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
        
        return lookupFunctionDeclaration(funcName) // Check for function symbol in declared functions
            .map((FuncDecl fdecl) -> checkFunction(fdecl, arguments)) // Check argument types match function declaration and return result type if true
            .orElse(Either.leftOf("Unknown function " + funcName)); // If function declaration not present
    }
    
    private Either<String, Type> visitQuantifier(Quantifier term) {
        
        // Check variables don't clash with function names
        for(AnnotatedVar av : term.getVars()) {
            if(lookupFunctionDeclaration(av.getName()).isPresent()) {
                return Either.leftOf("Variable name " + av.getName() + " conflicts with existing function symbol");
            }
        }
        
        Either<String, Type> result = checkBoolList(List.of(term.getBody()), term);
        return result;
    }
    
    @Override
    public Either<String, Type> visitExistsInner(Exists term) {
        return visitQuantifier(term);
    }
    
    @Override
    public Either<String, Type> visitForallInner(Forall term) {
        return visitQuantifier(term);
    }
    
}
