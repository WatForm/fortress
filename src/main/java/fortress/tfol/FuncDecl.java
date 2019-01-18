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
        
        this.name = name;
        this.argTypes = argTypes;
        this.resultType = resultType;
    }
    
    public int arity() {
        return argTypes.size();
    }
}
