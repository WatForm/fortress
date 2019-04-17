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
    private static class TypeCheckVisitor extends TermVisitorWithTypeContext<TypeCheckResult> {
        
        public TypeCheckVisitor(Signature signature) {
            super(signature);
        }
    
        @Override
        public TypeCheckResult visitTop(Top top) {
            return new TypeCheckResult(top, Type.Bool(),
                /* containsConnectives */ false, /* containsQuantifiers */ false);
        }
        
        @Override
        public TypeCheckResult visitBottom(Bottom bottom) {
            return new TypeCheckResult(bottom, Type.Bool(),
                /* containsConnectives */ false, /* containsQuantifiers */ false);
        }
        
        @Override
        public TypeCheckResult visitVar(Var variable) {
            // Check variable is not an already declared function symbol
            // This must be done even with a consistent signature
            // TODO: this behaviour should be documented
            // TODO: is this considered poorly typed or a different kind of error?
            if(signature.hasFunctionWithName(variable.getName())) {
                throw new TypeCheckException.NameConflict("Variable or constant name " + variable.getName() + " conflicts with existing function symbol");
            }
            
            // Check variable is not an already declared type symbol
            if(signature.hasTypeWithName(variable.getName())) {
                throw new TypeCheckException.NameConflict("Variable or constant name " + variable.getName() + " conflicts with existing type symbol");
            }
            
            Optional<Type> typeMaybe = lookupType(variable);
            if(typeMaybe.isPresent()) {
                return new TypeCheckResult(variable, typeMaybe.get(),
                    /* containsConnectives */ false, /* containsQuantifiers */ false);
            } else {
                throw new TypeCheckException.UndeterminedType("Could not determine type of variable " + variable.getName());
            }
        }
        
        @Override
        public TypeCheckResult visitNot(Not not) {
            TypeCheckResult bodyResult = visit(not.getBody());
            Term newBody = bodyResult.term;
            Type bodyType = bodyResult.type;
            if(bodyType.equals(Type.Bool())) {
                return new TypeCheckResult(Term.mkNot(newBody), Type.Bool(),
                    /* containsConnectives */ true, /* containsQuantifiers */ bodyResult.containsQuantifiers);
            } else {
                throw new TypeCheckException.WrongArgType("Argument of negation is of type " + bodyType.getName() + " in " + not.toString());
            }
        }

        @Override
        public TypeCheckResult visitAndList(AndList andList) {
            List<TypeCheckResult> results = andList.getArguments().stream().map(this::visit).collect(Collectors.toList());
            for(TypeCheckResult r : results) {
                if(! r.type.equals(Type.Bool())) {
                    throw new TypeCheckException.WrongArgType("Expected type Bool but was " + r.type.getName() + " in " + andList.toString());
                }
            }
            List<Term> newArguments = results.stream().map(r -> r.term).collect(Collectors.toList());
            boolean containsQuantifiers = results.stream().anyMatch((TypeCheckResult r) -> r.containsQuantifiers);
            return new TypeCheckResult(Term.mkAnd(newArguments), Type.Bool(),
                /* containsConnectives */ true, /* containsQuantifiers*/ containsQuantifiers);
        }
        
        @Override
        public TypeCheckResult visitOrList(OrList orList) {
            List<TypeCheckResult> results = orList.getArguments().stream().map(this::visit).collect(Collectors.toList());
            for(TypeCheckResult r : results) {
                if(! r.type.equals(Type.Bool())) {
                    throw new TypeCheckException.WrongArgType("Expected type Bool but was " + r.type.getName() + " in " + orList.toString());
                }
            }
            List<Term> newArguments = results.stream().map(r -> r.term).collect(Collectors.toList());
            boolean containsQuantifiers = results.stream().anyMatch((TypeCheckResult r) -> r.containsQuantifiers);
            return new TypeCheckResult(Term.mkOr(newArguments), Type.Bool(),
                /* containsConnectives */ true, /* containsQuantifiers*/ containsQuantifiers);
        }
        
        @Override
        public TypeCheckResult visitDistinct(Distinct distinct) {
            Set<Type> foundTypes = new HashSet<>();
            List<TypeCheckResult> results = distinct.getArguments().stream().map(this::visit).collect(Collectors.toList());
            
            for(TypeCheckResult result : results) {
                foundTypes.add(result.type);
            }
            
            if(foundTypes.size() > 1) {
                throw new TypeCheckException.WrongArgType("Arguments of multiple types " + foundTypes.toString() + " in " + distinct.toString());
            }
            
            List<Term> newArguments = results.stream().map(r -> r.term).collect(Collectors.toList());
            boolean containsQuantifiers = results.stream().anyMatch((TypeCheckResult r) -> r.containsQuantifiers);
            return new TypeCheckResult(Term.mkDistinct(newArguments), Type.Bool(),
                /* containsConnectives */ true, /* containsQuantifiers*/ containsQuantifiers);
        }
        
        @Override
        public TypeCheckResult visitImplication(Implication imp) {
            TypeCheckResult leftResult = visit(imp.getLeft());
            TypeCheckResult rightResult = visit(imp.getRight());
            if(! leftResult.type.equals(Type.Bool())) {
                throw new TypeCheckException.WrongArgType("Expected type Bool but was " + leftResult.type.getName() + " in " + imp.toString() );
            }
            if(! rightResult.type.equals(Type.Bool())) {
                throw new TypeCheckException.WrongArgType("Expected type Bool but was " + rightResult.type.getName() + " in " + imp.toString() );
            }
            boolean containsQuantifiers = leftResult.containsQuantifiers || rightResult.containsQuantifiers;
            return new TypeCheckResult(Term.mkImp(leftResult.term, rightResult.term), Type.Bool(),
                /* containsConnectives */ true, /* containsQuantifiers*/ containsQuantifiers);
        }
        @Override
        public TypeCheckResult visitIff(Iff iff) {
            TypeCheckResult leftResult = visit(iff.getLeft());
            TypeCheckResult rightResult = visit(iff.getRight());
            if(! leftResult.type.equals(Type.Bool())) {
                throw new TypeCheckException.WrongArgType("Expected type Bool but was " + leftResult.type.getName() + " in " + iff.toString() );
            }
            if(! rightResult.type.equals(Type.Bool())) {
                throw new TypeCheckException.WrongArgType("Expected type Bool but was " + rightResult.type.getName() + " in " + iff.toString() );
            }
            boolean containsQuantifiers = leftResult.containsQuantifiers || rightResult.containsQuantifiers;
            return new TypeCheckResult(Term.mkIff(leftResult.term, rightResult.term), Type.Bool(),
                /* containsConnectives */ true, /* containsQuantifiers*/ containsQuantifiers);
        }
        
        @Override
        public TypeCheckResult visitEq(Eq eq) {
            Set<Type> foundTypes = new HashSet<>();
            TypeCheckResult leftResult = visit(eq.getLeft());
            TypeCheckResult rightResult = visit(eq.getRight());
            
            if(! leftResult.type.equals(rightResult.type)) {
                throw new TypeCheckException.WrongArgType("Mismatched argument types " + leftResult.type.toString() + " and "
                    + rightResult.type.toString() + " in " + eq.toString());
            }
            boolean containsQuantifiers = leftResult.containsQuantifiers || rightResult.containsQuantifiers;
            // Replaces (Bool) = (Bool) with Iff
            if(leftResult.type.equals(Type.Bool())) {
                return new TypeCheckResult(Term.mkIff(leftResult.term, rightResult.term), Type.Bool(),
                    /* containsConnectives */ true, /* containsQuantifiers*/ containsQuantifiers);
            } else {
                return new TypeCheckResult(Term.mkEq(leftResult.term, rightResult.term), Type.Bool(),
                    /* containsConnectives */ true, /* containsQuantifiers*/ containsQuantifiers);
            }
        }
        
        // Check argument:
        // 1. types match function declaration
        // 2. arguments contain no connectives or quantifiers
        @Override
        public TypeCheckResult visitApp(App app) {
            String funcName = app.getFunctionName();
            
            if(!signature.hasFunctionWithName(funcName)) {
                throw new TypeCheckException.UnknownFunction("Could not find function " + funcName);
            }
            
            List<TypeCheckResult> results = app.getArguments().stream().map(this::visit).collect(Collectors.toList());
            List<Type> argTypes = results.stream().map(result -> result.type).collect(Collectors.toList());
            
            Optional<FuncDecl> funcMaybe = signature.queryFunctionJava(funcName, argTypes);
            if(!funcMaybe.isPresent()) {
                throw new TypeCheckException.WrongArgType(funcName + " cannot accept argument types " + argTypes.toString() + " in " + app.toString());
            }
            FuncDecl fdecl = funcMaybe.get();
            
            if(results.stream().anyMatch(result -> result.containsConnectives)) {
                throw new TypeCheckException.BadStructure("Argument of " + funcName + " contains connective");
            }
            if(results.stream().anyMatch(result -> result.containsQuantifiers)) {
                throw new TypeCheckException.BadStructure("Argument of " + funcName + " contains quantifier");
            }
            
            List<Term> newArguments = results.stream().map(r -> r.term).collect(Collectors.toList());
            return new TypeCheckResult(Term.mkApp(funcName, newArguments), fdecl.getResultType(),
                /* containsConnectives */ false, /* containsQuantifiers */ false);
        }
        
        @Override
        public TypeCheckResult visitExistsInner(Exists exists) {
            // Check variables don't clash with function names
            // and that their type exists
            for(AnnotatedVar av : exists.getVars()) {
                if(signature.hasFunctionWithName(av.getName())) {
                    throw new TypeCheckException.NameConflict("Variable name " + av.getName() + " conflicts with existing function symbol");
                }
                if(! signature.hasType(av.getType())) {
                    throw new TypeCheckException.UnknownType("Unknown type " + av.getType().getName() + " in " + exists.toString());
                }
            }
            
            TypeCheckResult bodyResult = visit(exists.getBody());
            if(bodyResult.type.equals(Type.Bool())) {
                return new TypeCheckResult(Term.mkExists(exists.getVars(), bodyResult.term), Type.Bool(),
                    /* containsConnective */ bodyResult.containsConnectives, /* containsQuantifiers */ true);
            } else {
                throw new TypeCheckException.WrongArgType("Expected Bool but was " + bodyResult.type.toString() + " in " + exists.toString());
            }
        }
        
        @Override
        public TypeCheckResult visitForallInner(Forall forall) {
            // Check variables don't clash with function names
            // and that their type exists
            for(AnnotatedVar av : forall.getVars()) {
                if(signature.hasFunctionWithName(av.getName())) {
                    throw new TypeCheckException.NameConflict("Variable name " + av.getName() + " conflicts with existing function symbol");
                }
                if(! signature.hasType(av.getType())) {
                    throw new TypeCheckException.UnknownType("Unknown type " + av.getType().getName() + " in " + forall.toString());
                }
            }
            
            TypeCheckResult bodyResult = visit(forall.getBody());
            if(bodyResult.type.equals(Type.Bool())) {
                return new TypeCheckResult(Term.mkForall(forall.getVars(), bodyResult.term), Type.Bool(),
                    /* containsConnectives */ bodyResult.containsConnectives, /* containsQuantifiers */ true);
            } else {
                throw new TypeCheckException.WrongArgType("Expected Bool but was " + bodyResult.type.toString() + " in " + forall.toString());
            }
        }
        
        @Override
        public TypeCheckResult visitDomainElement(DomainElement d) {
            Type type = d.sort();
            if(type.equals(Type.Bool())) {
                throw new TypeCheckException.WrongArgType("Cannot create domain element of type Bool");
            }
            if(!signature.hasType(type)) {
                throw new TypeCheckException.UnknownType("Unkown type " + type.toString() + " in " + d.toString());
            } else {
                return new TypeCheckResult(d, type, /* containsConnectives */ false, /* containsQuantifiers */ false);
            }
        }
        
        @Override
        public TypeCheckResult visitTC(TC tc) {
            String relationName = tc.relationName();
            if(!signature.hasFunctionWithName(relationName)) {
                throw new TypeCheckException.UnknownFunction("Unkown relation " + relationName + " in " + tc.toString());
            }
            
            
            TypeCheckResult arg1Result = visit(tc.arg1());
            TypeCheckResult arg2Result = visit(tc.arg2());
            if(arg1Result.containsConnectives || arg2Result.containsConnectives) {
                throw new TypeCheckException.BadStructure("Argument of " + tc.toString() + " contains connective");
            }
            if(arg1Result.containsQuantifiers || arg2Result.containsQuantifiers) {
                throw new TypeCheckException.BadStructure("Argument of " + tc.toString() + " contains quantifier");
            }
            if(! arg1Result.type.equals(arg2Result.type)) {
                throw new TypeCheckException.WrongArgType("Arguments of different types in " + tc.toString());
            }
            
            Type type = arg1Result.type;
            
            // Look for a relation A * A -> Bool
            Optional<FuncDecl> relationMaybe = signature.queryFunctionJava(relationName, List.of(type, type));
            if(relationMaybe.isPresent() && relationMaybe.get().getResultType().equals(Type.Bool())) {
                return new TypeCheckResult(Term.mkTC(relationName, arg1Result.term, arg2Result.term), Type.Bool(),
                    /* containsConnectives */ false, /* containsQuantifiers */ false);
            }
            
            // Look for a function A -> A
            Optional<FuncDecl> functionMaybe = signature.queryFunctionJava(relationName, List.of(type));
            if(functionMaybe.isPresent() && functionMaybe.get().getResultType().equals(type)) {
                return new TypeCheckResult(Term.mkTC(relationName, arg1Result.term, arg2Result.term), Type.Bool(),
                    /* containsConnectives */ false, /* containsQuantifiers */ false);
            }
            
            throw new TypeCheckException.UnknownFunction("Cannot find relation " + FuncDecl.mkFuncDecl(relationName, type, type, Type.Bool()).toString()
                + " or function " + FuncDecl.mkFuncDecl(relationName, type, type).toString() + " to take transitive closure of");
        }
        
        @Override
        public TypeCheckResult visitIntegerLiteral(IntegerLiteral literal) {
            return fortress.util.Errors.<TypeCheckResult>notImplemented();
        }
        
        @Override
        public TypeCheckResult visitBitVectorLiteral(BitVectorLiteral literal) {
            return fortress.util.Errors.<TypeCheckResult>notImplemented();
        }
    
    }
    
}
