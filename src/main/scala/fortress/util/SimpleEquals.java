package fortress.util;

import java.util.List;

public interface SimpleEquals {
    
    static boolean equal(SimpleEquals a, Object b) {
        // Template method design
        if(a == b) {
            return true;
        }
        if(null == b) {
            return null == a;
        }
        if(a.getClass() != b.getClass()) {
            return false;
        }
        return a.innerEquals(b);
    }
    
    // Given an object, guaranteed to be of the the same type, return
    // whether they are equal to this
    public abstract boolean innerEquals(Object other);
    
    static int hashCode(SimpleEquals obj) {
        // Template method design
        int prime = 31;
        int result = 1;
        for(int num : obj.innerHashNumbers()) {
            result = result * prime + num;
        }
        return result;
    }
    
    // List of numbers to be included when computing the hashCode
    // TODO consider making this an int[] instead for efficiency
    public abstract List<Integer> innerHashNumbers();
}
