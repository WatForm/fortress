package fortress.data;

import java.util.Set;
import java.util.HashSet;

public class SubIntNameGenerator implements NameGenerator {
    Set<String> forbiddenNames;
    
    public SubIntNameGenerator(Set<String> forbiddenNames) {
        this.forbiddenNames = new HashSet();
        // Copy the elements in case forbiddenNames changes
        this.forbiddenNames.addAll(forbiddenNames);
    }
    
    // TODO: could be implemented more efficiently in cases where we know
    // we are likely to use the same base often.
    
    public String freshName(String base) {
        int i = 0;
        String candidate = base + "_" + i;
        while(forbiddenNames.contains(candidate)) {
            i++;
            candidate = base + "_" + i;
        }
        forbiddenNames.add(candidate);
        return candidate;
    }
}
