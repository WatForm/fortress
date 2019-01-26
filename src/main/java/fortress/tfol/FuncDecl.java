package fortress.tfol;

import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

public class FuncDecl {
    private String name;
    private List<Type> argTypes;
    private Type resultType;
    
    public static FuncDecl mkFuncDecl(String name, List<Type> argTypes, Type resultType) {
        return new FuncDecl(name, argTypes, resultType);
    }
    
    public static FuncDecl mkFuncDecl(String name, Type... types) {
        Errors.failIf(types.length < 1);
        List<Type> argTypes = new ArrayList<>();
        Type resultType = types[types.length - 1];
        for(int i = 0; i < types.length - 1; i++) {
            argTypes.add(types[i]);
        }
        return mkFuncDecl(name, argTypes, resultType);
    }
    
    private FuncDecl(String name, List<Type> argTypes, Type resultType) {
        Errors.failIf(name.length() < 1);
        //TODO what about nullary functions?
        //I don't think these should fail here, but when used in App they are replaced
        
        // TODO may not need need type in FuncDecl depending on how we do typechecking
        
        this.name = name;
        this.argTypes = argTypes;
        this.resultType = resultType;
    }
    
    public int arity() {
        return argTypes.size();
    }
    
    public String getName() {
        return name;
    }
    
    public List<Type> getArgTypes() {
        return argTypes;
    }
    
    public Type getResultType() {
        return resultType;
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
        FuncDecl o = (FuncDecl) other;
        return this.name.equals(o.name)
            && this.argTypes.equals(o.argTypes)
            && this.resultType.equals(o.resultType);
    }
    
    @Override
    public int hashCode() {
        int prime = 31;
        int result = 1;
        result = result * prime + name.hashCode();
        result = result * prime + argTypes.hashCode();
        result = result * prime + resultType.hashCode();
        return result;
    }
}
