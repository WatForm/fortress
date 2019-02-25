package fortress.data;

public interface NameGenerator {
    
    // This method is expected to mutate the name generator
    // and forbid the resulting name from being used in the future
    public String freshName(String base);
}
