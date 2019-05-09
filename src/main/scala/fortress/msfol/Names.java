package fortress.msfol;

import java.util.Set;
import java.util.HashSet;
import java.util.Arrays;

public class Names {
    private static Set<String> illegalNames = new HashSet<>(Arrays.asList(
        "and", "or", "not", "=>", "<=>", "iff",
        "forall", "exists", "=", "==",
        "true", "false", 
        "if", "else"
    ));
    
    public static boolean isIllegal(String name) {
        return illegalNames.contains(name.toLowerCase());
    }
}
