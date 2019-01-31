package fortress.tfol;

import java.util.Set;
import java.util.HashSet;
import java.util.Map;
import java.util.HashMap;
import fortress.util.Errors;
import java.io.*;

public class Theory {
    private Set<Term> axioms;
    private Set<Var> constants;
    private Set<FuncDecl> functionSymbols;
    private Set<Type> types;
    private Map<Type, Integer> scopes; // Optional scopes for types
    // You are allowed to have a combination of scoped and unscoped types
    
    public Theory() {
        // TODO hash set or tree set?
        this.axioms = new HashSet<>();
        this.constants = new HashSet<>();
        this.functionSymbols = new HashSet<>();
        this.types = new HashSet<>();
        this.scopes = new HashMap<>();
        types.add(Type.Bool);
    }
    
    public void addAxiom(Term formula) {
        axioms.add(formula);
    }
    
    public void addConstant(Var constant) {
        constants.add(constant);
    }
    
    public void addType(Type type) {
        types.add(type);
    }
    
    public void addFunctionSymbol(FuncDecl f) {
        functionSymbols.add(f);
    }
    
    public void addScope(Type type, int scope) {
        Errors.failIf(!types.contains(type));
        Errors.failIf(scope < 1);
        scopes.put(type, scope);
    }
    
    public Set<Term> getAxioms() {
        return axioms;
    }
    
    public Set<Type> getTypes() {
        return types;
    }
    
    public Set<FuncDecl> getFunctionSymbols() {
        return functionSymbols;
    }
    
    public Set<Var> getConstants() {
        return constants;
    }
    
    public Map<Type, Integer> getScopes() {
        return scopes;
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
