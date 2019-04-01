package fortress.data;

import java.util.Set;
import java.util.HashSet;

public class SubIntNameGenerator implements NameGenerator {
    private Set<String> forbiddenNames;
    private int startingIndex;
    
    public SubIntNameGenerator(Set<String> forbiddenNames, int startingIndex) {
        // Copy the elements in case forbiddenNames changes
        this.forbiddenNames = new HashSet<>(forbiddenNames);
        this.startingIndex = startingIndex;
    }
    
    // TODO: could be implemented more efficiently in cases where we know
    // we are likely to use the same base often.
    @Override
    public String freshName(String base) {
        int i = startingIndex;
        String candidate = base + "_" + i;
        while(forbiddenNames.contains(candidate)) {
            i++;
            candidate = base + "_" + i;
        }
        forbiddenNames.add(candidate);
        return candidate;
    }
    @Override
    public void forbidName(String name) {
        forbiddenNames.add(name);
    }
}
