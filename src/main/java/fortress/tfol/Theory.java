package fortress.tfol;

import fortress.data.PersistentSet;
import fortress.data.PersistentHashSet;
import java.util.Set;
import fortress.util.Errors;
import java.io.*;
import java.util.Optional;
import java.util.stream.Collectors;
import java.lang.Iterable;

import fortress.modelfind.*;

public class Theory {
    private PersistentSet<Term> axioms;
    private PersistentSet<AnnotatedVar> constants;
    private PersistentSet<FuncDecl> functionDeclarations;
    private PersistentSet<Type> types;
    
    public Theory() {
        // TODO hash set or tree set?
        this.axioms = PersistentHashSet.empty();
        this.constants = PersistentHashSet.empty();
        this.functionDeclarations = PersistentHashSet.empty();
        this.types = PersistentHashSet.empty().plus(Type.Bool);
    }
    
    private Theory(PersistentSet<Term> axioms,
        PersistentSet<AnnotatedVar> constants,
        PersistentSet<FuncDecl> functionDeclarations,
        PersistentSet<Type> types) {
            this.axioms = axioms;
            this.constants = constants;
            this.functionDeclarations = functionDeclarations;
            this.types = types.plus(Type.Bool);
        }
    
    // Mutates this theory object
    public void addAxiom(Term formula) {
        checkAxiom(formula);
        axioms = axioms.plus(formula);
    }
    // Returns a new theory object without modifying the previous
    public Theory withAxiom(Term formula) {
        checkAxiom(formula);
        return new Theory(axioms.plus(formula), constants, functionDeclarations, types);
    }
    
    // Mutates this theory object
    public void addType(Type type) {
        types = types.plus(type);
    }
    // Returns a new theory object without modifying the previous
    public Theory withType(Type type) {
        return new Theory(axioms, constants, functionDeclarations, types.plus(type));
    }
    
    // Mutates this theory object
    public void addConstant(AnnotatedVar constant) {
        assertConstIsConsistent(constant);
        constants = constants.plus(constant);
    }
    // Returns a new theory object without modifying the previous
    public Theory withConstant(AnnotatedVar constant) {
        assertConstIsConsistent(constant);
        return new Theory(axioms, constants.plus(constant), functionDeclarations, types);
    }
    
    // Mutates this theory object
    public void addFunctionDeclaration(FuncDecl f) {
        assertFuncDeclIsConsistent(f);
        functionDeclarations = functionDeclarations.plus(f);
    }
    // Returns a new theory object without modifying the previous
    public Theory withFunctionDeclaration(FuncDecl f) {
        assertFuncDeclIsConsistent(f);
        return new Theory(axioms, constants, functionDeclarations.plus(f), types);
    }
    
    public Set<Term> getAxioms() {
        return axioms;
    }
    
    public Set<Type> getTypes() {
        return types;
    }
    
    public Set<AnnotatedVar> getConstants() {
        return constants;
    }
    
    public Set<FuncDecl> getFunctionDeclarations() {
        return functionDeclarations;
    }
    
    private void checkAxiom(Term formula) {
        // Check axiom typechecks as bool
        Errors.failIf(! Term.typeCheck(formula, types, constants, functionDeclarations)
            .equals(Optional.of(Type.Bool)));
        // TODO efficiency
        Set<Var> asVars = constants.stream().map(av -> av.getVar()).collect(Collectors.toSet());
        Errors.failIf(! asVars.containsAll(Term.freeVariables(formula)));
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
        Errors.failIf(!types.containsValue(c.getType())); // type exists in theory
        Errors.failIf(!constants.stream().allMatch(otherConst -> consistent(c, otherConst))); // doesn't conflict with other constants
        Errors.failIf(!functionDeclarations.stream().allMatch(f -> consistent(f, c))); // doesn't conflict with function names
    }
    
    private void assertFuncDeclIsConsistent(FuncDecl f) {
        Errors.failIf(!f.getArgTypes().stream().allMatch(types::containsValue)); // arg types exist in theory
        Errors.failIf(!types.containsValue(f.getResultType())); // result type exists in theory
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
            && this.types.equals(o.types);
    }
    
    @Override
    public int hashCode() {
        int prime = 31;
        int result = 1;
        result = result * prime + axioms.hashCode();
        result = result * prime + constants.hashCode();
        result = result * prime + functionDeclarations.hashCode();
        result = result * prime + types.hashCode();
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
