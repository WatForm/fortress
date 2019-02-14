package fortress.tfol;

import java.util.List;

// TODO Does type need subclasses?
// While I do think the constructor should be protected in case we
// change implementation, I never
// see a need for any kinds of types other than TypeConst for our purposes
// If I do change it, need to decide whether to change classes that use type.toString()
// to just get the name

public abstract class Type {
    public static Type mkTypeConst(String name) {
        return new TypeConst(name);
    }
    
    public static Type Bool = mkTypeConst("Bool");
    
    // TODO should have getName() rather than just toString() for consistency
    
    @Override
    public abstract String toString();
    
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
        return innerEquals(other);
    }
    
    // Given an object, guaranteed to be a term of the the same subtype, return
    // whether they are equal to this
    protected abstract boolean innerEquals(Object other);
    
    @Override
    public int hashCode() {
        // Template method design
        int prime = 31;
        int result = 1;
        for(int num : innerHashNumbers()) {
            result = result * prime + num;
        }
        return result;
    }
    
    // List of numbers to be included when computing the hashCode
    protected abstract List<Integer> innerHashNumbers();
}
