package fortress.tfol;

import fortress.util.Errors;
import java.io.*;
import cyclops.data.ImmutableSet;
import cyclops.data.ImmutableMap;
import cyclops.data.HashSet;
import cyclops.data.HashMap;

public class Theory {
    private ImmutableSet<Term> axioms;
    private ImmutableSet<AnnotatedVar> constants;
    private ImmutableSet<FuncDecl> functionDeclarations;
    private ImmutableSet<Type> types;
    private ImmutableMap<Type, Integer> scopes; // Optional scopes for types
    // You are allowed to have a combination of scoped and unscoped types
    
    public Theory() {
        // TODO hash set or tree set?
        this.axioms = HashSet.empty();
        this.constants = HashSet.empty();
        this.functionDeclarations = HashSet.empty();
        this.types = HashSet.of(Type.Bool);
        this.scopes = HashMap.empty();
    }
    
    private Theory(ImmutableSet<Term> axioms,
        ImmutableSet<AnnotatedVar> constants,
        ImmutableSet<FuncDecl> functionDeclarations,
        ImmutableSet<Type> types,
        ImmutableMap<Type, Integer> scopes) {
            this.axioms = axioms;
            this.constants = constants;
            this.functionDeclarations = functionDeclarations;
            this.types = types.plus(Type.Bool);
            this.scopes = scopes;
        }
    
    // Mutates this theory object
    public void addAxiom(Term formula) {
        axioms = axioms.plus(formula);
    }
    // Returns a new theory object without modifying the previous
    public Theory withAxiom(Term formula) {
        return new Theory(axioms.plus(formula), constants, functionDeclarations, types, scopes);
    }
    
    // Mutates this theory object
    public void addType(Type type) {
        types = types.plus(type);
    }
    // Returns a new theory object without modifying the previous
    public Theory withType(Type type) {
        return new Theory(axioms, constants, functionDeclarations, types.plus(type), scopes);
    }
    
    // Mutates this theory object
    public void addConstant(AnnotatedVar constant) {
        assertConstIsConsistent(constant);
        constants = constants.plus(constant);
    }
    // Returns a new theory object without modifying the previous
    public Theory withConstant(AnnotatedVar constant) {
        assertConstIsConsistent(constant);
        return new Theory(axioms, constants.plus(constant), functionDeclarations, types, scopes);
    }
    
    // Mutates this theory object
    public void addFunctionDeclaration(FuncDecl f) {
        assertFuncDeclIsConsistent(f);
        functionDeclarations = functionDeclarations.plus(f);
    }
    // Returns a new theory object without modifying the previous
    public Theory withFunctionDeclaration(FuncDecl f) {
        assertFuncDeclIsConsistent(f);
        return new Theory(axioms, constants, functionDeclarations.plus(f), types, scopes);
    }
    
    // Mutates this theory object
    public void addScope(Type type, int scope) {
        Errors.failIf(!types.contains(type));
        Errors.failIf(scope < 1);
        scopes = scopes.put(type, scope);
    }
    // Returns a new theory object without modifying the previous
    public Theory withScope(Type type, int scope) {
        Errors.failIf(!types.contains(type));
        Errors.failIf(scope < 1);
        return new Theory(axioms, constants, functionDeclarations, types, scopes.put(type, scope));
    }
    
    
    // Not published
    public ImmutableSet<Term> getAxioms() {
        return axioms;
    }
    
    public ImmutableSet<Type> getTypes() {
        return types;
    }
    
    public ImmutableSet<FuncDecl> getFunctionDeclarations() {
        return functionDeclarations;
    }
    
    public ImmutableSet<AnnotatedVar> getConstants() {
        return constants;
    }
    
    public ImmutableMap<Type, Integer> getScopes() {
        return scopes;
    }
    
    private boolean consistent(AnnotatedVar const1, AnnotatedVar const2) {
        return const1.getName() != const2.getName()
            || const1.equals(const2);
    }
    
    private boolean consistent(FuncDecl f1, FuncDecl f2) {
        return f1.getName() != f2.getName()
            || f1.equals(f2);
    }
    
    private boolean consistent(FuncDecl f, AnnotatedVar c) {
        return f.getName() != c.getName();
    }
    
    private void assertConstIsConsistent(AnnotatedVar c) {
        Errors.failIf(!types.contains(c.getType())); // type exists in theory
        Errors.failIf(!constants.stream().allMatch(otherConst -> consistent(c, otherConst))); // doesn't conflict with other constants
        Errors.failIf(!functionDeclarations.stream().allMatch(f -> consistent(f, c))); // doesn't conflict with function names
    }
    
    private void assertFuncDeclIsConsistent(FuncDecl f) {
        Errors.failIf(!f.getArgTypes().stream().allMatch(types::contains)); // arg types exist in theory
        Errors.failIf(!types.contains(f.getResultType())); // result type exists in theory
        Errors.failIf(!constants.stream().allMatch(c -> consistent(f, c))); // doesn't conflict with constants
        Errors.failIf(!functionDeclarations.stream().allMatch(otherFun -> consistent(f, otherFun))); // doesn't conflict with other function declarations
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
        Theory o = (Theory) other;
        return this.axioms.equals(o.axioms)
            && this.constants.equals(o.constants)
            && this.functionDeclarations.equals(o.functionDeclarations)
            && this.types.equals(o.types)
            && this.scopes.equals(o.scopes);
    }
    
    @Override
    public int hashCode() {
        int prime = 31;
        int result = 1;
        result = result * prime + axioms.hashCode();
        result = result * prime + constants.hashCode();
        result = result * prime + functionDeclarations.hashCode();
        result = result * prime + types.hashCode();
        result = result * prime + scopes.hashCode();
        return result;
    }
    
    //Testing only
    @Override
    public String toString() {
        try {
            StringWriter stringWriter = new StringWriter();
            BufferedWriter bufferedWriter = new BufferedWriter(stringWriter);
            Z3CommandLine.writeSmtLib(this, bufferedWriter);
            bufferedWriter.flush();
            bufferedWriter.close();
            return stringWriter.toString();
        } catch(IOException e) {
            return "ERROR-STRING";
        }
    }
    
}
