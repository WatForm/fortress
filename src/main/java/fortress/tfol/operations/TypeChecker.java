package fortress.tfol.operations;

import java.util.Optional;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.Set;
import java.util.HashSet;
import fortress.tfol.*;
import java.util.Iterator;
import fortress.util.Pair;
import fortress.data.ImmutableList;
import fortress.data.TypeCheckException;

public class TypeChecker {
    
    public TypeChecker() { }
    
    /**
     * Given a signature and a term, typechecks the term with respect to the signature.
     * Returns a TypeCheckResult containing the type of the term, AND a new term
     * that is equal to the old term but with instances of Eq replaced with Iff
     * when comparing Bool types. Such a term is called "sanitized".
    */
    public static TypeCheckResult typeCheck(Signature signature, Term term) {
        return new TypeCheckVisitor(signature).visit(term);
    }
    
    // Visitor interface hidden -- the fact that it uses a visitor is
    // just an implementation detail
    private static class TypeCheckVisitor extends TermVisitorWithContext<TypeCheckResult> {
        
        public TypeCheckVisitor(Signature signature) {
            super(signature);
        }
    
        @Override
        public TypeCheckResult visitTop(Top top) {
            return new TypeCheckResult(top, Type.Bool);
        }
        
        @Override
        public TypeCheckResult visitBottom(Bottom bottom) {
            return new TypeCheckResult(bottom, Type.Bool);
        }
        
        @Override
        public TypeCheckResult visitVar(Var variable) {
            // Check variable is not an already declared function symbol
            // This must be done even with a consistent signature
            // TODO: this behaviour should be documented
            // TODO: is this considered poorly typed or a different kind of error?
            if(lookupFunctionDeclaration(variable.getName()).isPresent()) {
                throw new TypeCheckException("Variable or constant name " + variable.getName() + " conflicts with existing function symbol");
            }
            
            Optional<Type> typeMaybe = lookupType(variable);
            if(typeMaybe.isPresent()) {
                return new TypeCheckResult(variable, typeMaybe.get());
            } else {
                throw new TypeCheckException("Could not determine type of variable " + variable.getName());
            }
        }
        
        @Override
        public TypeCheckResult visitNot(Not not) {
            TypeCheckResult bodyResult = visit(not.getBody());
            Term newBody = bodyResult.term;
            Type bodyType = bodyResult.type;
            if(bodyType.equals(Type.Bool)) {
                return new TypeCheckResult(Term.mkNot(newBody), Type.Bool);
            } else {
                throw new TypeCheckException("Argument of negation is of type " + bodyType.getName() + " in " + not.toString());
            }
        }

        @Override
        public TypeCheckResult visitAndList(AndList andList) {
            ImmutableList<TypeCheckResult> results = andList.getArguments().map(this::visit);
            for(TypeCheckResult r : results) {
                if(! r.type.equals(Type.Bool)) {
                    throw new TypeCheckException("Expected type Bool but was " + r.type.getName() + " in " + andList.toString());
                }
            }
            ImmutableList<Term> newArguments = results.map(r -> r.term);
            return new TypeCheckResult(Term.mkAndF(newArguments), Type.Bool);
        }
        
        @Override
        public TypeCheckResult visitOrList(OrList orList) {
            ImmutableList<TypeCheckResult> results = orList.getArguments().map(this::visit);
            for(TypeCheckResult r : results) {
                if(! r.type.equals(Type.Bool)) {
                    throw new TypeCheckException("Expected type Bool but was " + r.type.getName() + " in " + orList.toString());
                }
            }
            ImmutableList<Term> newArguments = results.map(r -> r.term);
            return new TypeCheckResult(Term.mkOrF(newArguments), Type.Bool);
        }
        
        @Override
        public TypeCheckResult visitDistinct(Distinct distinct) {
            Set<Type> foundTypes = new HashSet();
            ImmutableList<TypeCheckResult> results = distinct.getArguments().map(this::visit);
            
            for(TypeCheckResult result : results) {
                foundTypes.add(result.type);
            }
            
            if(foundTypes.size() > 1) {
                throw new TypeCheckException("Arguments of multiple types " + foundTypes.toString() + " in " + distinct.toString());
            }
            
            ImmutableList<Term> newArguments = results.map(r -> r.term);
            return new TypeCheckResult(Term.mkDistinctF(newArguments), Type.Bool);
        }
        
        @Override
        public TypeCheckResult visitImplication(Implication imp) {
            TypeCheckResult leftResult = visit(imp.getLeft());
            TypeCheckResult rightResult = visit(imp.getRight());
            if(! leftResult.type.equals(Type.Bool)) {
                throw new TypeCheckException("Expected type Bool but was " + leftResult.type.getName() + " in " + imp.toString() );
            }
            if(! rightResult.type.equals(Type.Bool)) {
                throw new TypeCheckException("Expected type Bool but was " + rightResult.type.getName() + " in " + imp.toString() );
            }
            return new TypeCheckResult(Term.mkImp(leftResult.term, rightResult.term), Type.Bool);
        }
        @Override
        public TypeCheckResult visitIff(Iff iff) {
            TypeCheckResult leftResult = visit(iff.getLeft());
            TypeCheckResult rightResult = visit(iff.getRight());
            if(! leftResult.type.equals(Type.Bool)) {
                throw new TypeCheckException("Expected type Bool but was " + leftResult.type.getName() + " in " + iff.toString() );
            }
            if(! rightResult.type.equals(Type.Bool)) {
                throw new TypeCheckException("Expected type Bool but was " + rightResult.type.getName() + " in " + iff.toString() );
            }
            return new TypeCheckResult(Term.mkIff(leftResult.term, rightResult.term), Type.Bool);
        }
        
        @Override
        public TypeCheckResult visitEq(Eq eq) {
            Set<Type> foundTypes = new HashSet();
            TypeCheckResult leftResult = visit(eq.getLeft());
            TypeCheckResult rightResult = visit(eq.getRight());
            
            if(! leftResult.type.equals(rightResult.type)) {
                throw new TypeCheckException("Mismatched argument types " + leftResult.type.toString() + " and "
                    + rightResult.type.toString() + " in " + eq.toString());
            }
            
            // Replaces (Bool) = (Bool) with Iff
            if(leftResult.type.equals(Type.Bool)) {
                return new TypeCheckResult(Term.mkIff(leftResult.term, rightResult.term), Type.Bool);
            } else {
                return new TypeCheckResult(Term.mkEq(leftResult.term, rightResult.term), Type.Bool);
            }
        }
        
        private TypeCheckResult checkFunction(FuncDecl funcDecl, ImmutableList<Term> arguments) {
            if(funcDecl.getArity() != arguments.size()) {
                throw new TypeCheckException("Application of " + funcDecl.getName() + " to wrong number of arguments");
            }
            
            ImmutableList<TypeCheckResult> results = arguments.map(this::visit);
            
            Iterator<Type> itTypes = funcDecl.getArgTypes().iterator();
            Iterator<TypeCheckResult> itResults = results.iterator();
            int argNum = 0;
            while(itTypes.hasNext() && itResults.hasNext()) {
                argNum++;
                Type expected = itTypes.next();
                Type actual = itResults.next().type;
                if(!expected.equals(actual)) {
                    throw new TypeCheckException("In argument " + argNum + " of " + funcDecl.getName() + ", expected " + expected.getName() + " but was " + actual.getName());
                }
            }
            
            ImmutableList<Term> newArguments = results.map(r -> r.term);
            return new TypeCheckResult(Term.mkAppF(funcDecl.getName(), newArguments), funcDecl.getResultType());
        }
        
        @Override
        public TypeCheckResult visitApp(App app) {
            String funcName = app.getFunctionName();
            
            // Check for function symbol in declared functions
            Optional<FuncDecl> fMaybe = lookupFunctionDeclaration(funcName);
            if(! fMaybe.isPresent()) {
                throw new TypeCheckException("Unknown function " + funcName);
            } else {
                FuncDecl fdecl = fMaybe.get();
                // Check argument types match function declaration and return result type if true
                return checkFunction(fdecl, app.getArguments());
            }
        }
        
        @Override
        public TypeCheckResult visitExistsInner(Exists exists) {
            // Check variables don't clash with function names
            for(AnnotatedVar av : exists.getVars()) {
                if(lookupFunctionDeclaration(av.getName()).isPresent()) {
                    throw new TypeCheckException("Variable name " + av.getName() + " conflicts with existing function symbol");
                }
            }
            
            TypeCheckResult result = visit(exists.getBody());
            if(result.type.equals(Type.Bool)) {
                return new TypeCheckResult(Term.mkExists(exists.getVars(), result.term), Type.Bool);
            } else {
                throw new TypeCheckException("Expected Bool but was " + result.type.toString() + " in " + exists.toString());
            }
        }
        
        @Override
        public TypeCheckResult visitForallInner(Forall forall) {
            // Check variables don't clash with function names
            for(AnnotatedVar av : forall.getVars()) {
                if(lookupFunctionDeclaration(av.getName()).isPresent()) {
                    throw new TypeCheckException("Variable name " + av.getName() + " conflicts with existing function symbol");
                }
            }
            
            TypeCheckResult result = visit(forall.getBody());
            if(result.type.equals(Type.Bool)) {
                return new TypeCheckResult(Term.mkForall(forall.getVars(), result.term), Type.Bool);
            } else {
                throw new TypeCheckException("Expected Bool but was " + result.type.toString() + " in " + forall.toString());
            }
        }
    
    }
    
}
