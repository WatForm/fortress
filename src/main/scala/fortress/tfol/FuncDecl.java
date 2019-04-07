package fortress.tfol;

import fortress.data.ImmutableList;
import fortress.data.ImmutableWrapperList;
import java.util.List;
import java.util.ArrayList;
import fortress.util.Errors;

public class FuncDecl {
    private String name;
    private ImmutableList<Type> argTypes;
    private Type resultType;
    
    private FuncDecl(String name, ImmutableList<Type> argTypes, Type resultType) {
        Errors.precondition(argTypes.size() > 0, "Cannot create nullary functions; use a constant instead");
        Errors.precondition(! Names.isIllegal(name), "Illegal function name " + name);
        Errors.precondition(name.length() > 0, "Cannot create function with empty name");
        
        this.name = name;
        this.argTypes = argTypes;
        this.resultType = resultType;
    }
    
    public static FuncDecl mkFuncDecl(String name, List<Type> argTypes, Type resultType) {
        return new FuncDecl(name, ImmutableWrapperList.copyCollection(argTypes), resultType);
    }
    
    public static FuncDecl mkFuncDecl(String name, Type... types) {
        List<Type> argTypes = new ArrayList<>();
        Type resultType = types[types.length - 1];
        for(int i = 0; i < types.length - 1; i++) {
            argTypes.add(types[i]);
        }
        return mkFuncDecl(name, argTypes, resultType);
    }
    
    public int getArity() {
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
