package fortress.tfol;

import fortress.data.PersistentSet;
import fortress.data.PersistentHashSet;
import fortress.data.PersistentInsertionOrderedHashSet;
import java.util.Optional;
import java.util.Set;
import fortress.util.Errors;

// Persistent and Immutable
// Internally consistent
public class Signature {
    private final PersistentSet<Type> types;
    private final PersistentSet<FuncDecl> functionDeclarations;
    private final PersistentSet<AnnotatedVar> constants;
    
    private Signature(PersistentSet<Type> types,
                      PersistentSet<FuncDecl> functionDeclarations,
                      PersistentSet<AnnotatedVar> constants) {
        this.types = types;
        this.functionDeclarations = functionDeclarations;
        this.constants = constants;
    }
    
    public static Signature empty() {
        // For testing consistency, use an insertion ordered set
        return new Signature(
            PersistentInsertionOrderedHashSet.empty().plus(Type.Bool), // Every signature contains Bool
            PersistentInsertionOrderedHashSet.empty(),
            PersistentInsertionOrderedHashSet.empty()
        );
    }
    
    public Signature withType(Type t) {
        assertTypeConsistent(t);
        return new Signature(types.plus(t), functionDeclarations, constants);
    }
    
    public Signature withTypes(Iterable<Type> types) {
        Signature sig = this;
        for(Type t : types) {
            sig = sig.withType(t);
        }
        return sig;
    }
    
    public Signature withTypes(Type... types) {
        Signature sig = this;
        for(Type t : types) {
            sig = sig.withType(t);
        }
        return sig;
    }
    
    public Signature withFunctionDeclaration(FuncDecl fdecl) {
        assertFuncDeclConsistent(fdecl);
        return new Signature(types, functionDeclarations.plus(fdecl), constants);
    }
    
    public Signature withFunctionDeclarations(Iterable<FuncDecl> fdecls) {
        Signature sig = this;
        for(FuncDecl f : fdecls) {
            sig = sig.withFunctionDeclaration(f);
        }
        return sig;
    }
    
    public Signature withFunctionDeclarations(FuncDecl... fdecls) {
        Signature sig = this;
        for(FuncDecl f : fdecls) {
            sig = sig.withFunctionDeclaration(f);
        }
        return sig;
    }
    
    public Signature withConstant(AnnotatedVar c) {
        assertConstConsistent(c);
        return new Signature(types, functionDeclarations, constants.plus(c));
    }
    
    public Signature withConstants(Iterable<AnnotatedVar> constants) {
        Signature sig = this;
        for(AnnotatedVar c : constants) {
            sig = sig.withConstant(c);
        }
        return sig;
    }
    
    public Signature withConstants(AnnotatedVar... constants) {
        Signature sig = this;
        for(AnnotatedVar c : constants) {
            sig = sig.withConstant(c);
        }
        return sig;
    }
    
    public Optional<AnnotatedVar> lookupConstant(Var v) {
        return constants.stream()
            .filter(c -> c.getVar().equals(v))
            .findAny();
    }
    
    public Optional<FuncDecl> lookupFunctionDeclaration(String functionName) {
        return functionDeclarations.stream()
            .filter(fdecl -> fdecl.getName().equals(functionName))
            .findAny();
    }
    
    public boolean hasType(String name) {
        return types.containsValue(Type.mkTypeConst(name));
    }
    
    public boolean hasType(Type type) {
        return types.containsValue(type);
    }
    
    /* Package private */ Set<AnnotatedVar> getConstants() {
        return constants;
    }
    
    /* Package private */ Set<FuncDecl> getFunctionDeclarations() {
        return functionDeclarations;
    } 
    
    /* Package private */ Set<Type> getTypes() {
        return types;
    } 
    
    private void assertTypeConsistent(Type t) {
        // Type must not share a name with any function
        Errors.precondition(! functionDeclarations.stream().anyMatch(
            (FuncDecl fdecl) -> fdecl.getName().equals(t.getName())
        ), "Name " + t.getName() + " shared by type and function");
        
        // Type must not share a name with any constant
        Errors.precondition(! constants.stream().anyMatch(
            (AnnotatedVar c) -> c.getName().equals(t.getName())
        ), "Name " + t.getName() + " shared by type and constant");
    }
    
    private void assertConstConsistent(AnnotatedVar c) {
        // Constant's type must be within the set of types
        Errors.precondition(types.containsValue(c.getType()),
            "Constant " + c.getName() + " of undeclared type " + c.getType().getName());
        
        // Constant's cannot share a name with a constant of a different type
        Errors.precondition(! constants.stream().anyMatch(
            (AnnotatedVar otherConst) -> otherConst.getName().equals(c.getName()) && !otherConst.equals(c)
        ), "Constant " + c.getName() + " declared with two different types");
        
        // Constant cannot share a name with any function 
        Errors.precondition(! functionDeclarations.stream().anyMatch(
            (FuncDecl fdecl) -> fdecl.getName().equals(c.getName())
        ), "Name " + c.getName() + " shared by constant and function");
    }
    
    private void assertFuncDeclConsistent(FuncDecl fdecl) {
        // Argument types must exist in type set
        Errors.precondition(fdecl.getArgTypes().stream().allMatch(types::containsValue),
            "Function " + fdecl.getName() + " has argument types that are undeclared");
            
        // Result type must exist in type set
        Errors.precondition(types.containsValue(fdecl.getResultType()),
            "Function " + fdecl.getName() + " has result type that is undeclared");
            
        // Function must not share name with a constant
        Errors.precondition(! constants.stream().anyMatch(
            (AnnotatedVar c) -> c.getName().equals(fdecl.getName())
        ), "Name " + fdecl.getName() +  " shared by function and constant");
        
        // Function must not share name with a type
        Errors.precondition(! types.stream().anyMatch(
            (Type type) -> type.getName().equals(fdecl.getName())
        ), "Name " + fdecl.getName() +  " shared by function and type");
        
        // Function must not share name with another function, unless it is the same function
        Errors.precondition(! functionDeclarations.stream().anyMatch(
            (FuncDecl otherFun) -> otherFun.getName().equals(fdecl.getName()) && ! otherFun.equals(fdecl)
        ), "Function " + fdecl.getName() + " declared with two different types");
    }
    
    @Override
    public boolean equals(Object other) {
        if(this == other) {
            return true;
        }
        if(null == other) {
            return false;
        }
        if(this.getClass() != other.getClass()) {
            return false;
        }
        Signature o = (Signature) other;
        return this.constants.equals(o.constants)
            && this.functionDeclarations.equals(o.functionDeclarations)
            && this.types.equals(o.types);
        
    }
    
    @Override
    public int hashCode() {
        int prime = 31;
        int result = 1;
        result = result * prime + constants.hashCode();
        result = result * prime + functionDeclarations.hashCode();
        result = result * prime + types.hashCode();
        return result;
    }
}
