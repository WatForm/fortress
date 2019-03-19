package fortress.tfol;

import fortress.util.Errors;
import fortress.tfol.operations.TermVisitor;

/**
* @publish
* Represents a type, sometimes called a sort.
*/
public class Type {
    
    // Published Interface
    
    /**
    * @publish
    * Returns a Type with the given name.
    */
    public static Type mkTypeConst(String name) {
        Errors.failIf(name.length() < 1, "Cannot create type with empty name");
        Errors.failIf(Names.isIllegal(name), "Illegal type name " + name);
        return new Type(name);
    }
    
    // End of Published Interface
    private final String name;
    
    private Type(String name) {
        this.name = name;
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
