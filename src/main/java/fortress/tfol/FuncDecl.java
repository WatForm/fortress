package fortress.tfol;

import java.util.List;
import fortress.util.Errors;

public class FuncDecl {
    private String name;
    private List<Type> argTypes;
    private Type resultType;
    
    public FuncDecl(String name, List<Type> argTypes, Type resultType) {
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
