import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import fortress.data.PersistentSet;
import fortress.data.PersistentHashSet;
import java.util.Set;
import java.util.List;

public class PersistentHashSetTest {
    
    @Test
    public void equalityWithSets() {
        PersistentSet<Integer> s1 = PersistentHashSet.empty();
        PersistentSet<Integer> s2 = s1.plus(5);
        PersistentSet<Integer> s3 = s2.plusAll(List.of(6, 5, 6, 7, 8));
        
        assertTrue(Set.of().equals(s1));
        assertTrue(s1.equals(Set.of()));
        
        assertTrue(Set.of(5).equals(s2));
        assertTrue(s2.equals(Set.of(5)));
        
        assertTrue(Set.of(5, 6, 7, 8).equals(s3));
        assertTrue(s3.equals(Set.of(5, 6, 7, 8)));
    }
}
