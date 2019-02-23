package fortress.tfol;

import fortress.util.Errors;
import fortress.tfol.visitor.TermVisitor;

public class Type {
    private final String name;
    
    private Type(String name) {
        Errors.failIf(name.length() < 1);
        this.name = name;
    }
    
    public static Type mkTypeConst(String name) {
        return new Type(name);
    }
    
    public static Type Bool = mkTypeConst("Bool");
    
    public String getName() {
        return name;
    }
    
    @Override
    public String toString() {
        return name;
    }
    
    @Override
    public boolean equals(Object other) {
        // Template method design
        if(this == other) {
            return true;
        }
        if(null == other) {
            return false;
        }
        if(this.getClass() != other.getClass()) {
            return false;
        }
        return this.name.equals( ((Type)other).getName() );
    }
    
    @Override
    public int hashCode() {
        return name.hashCode();
    }
}
