import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import org.junit.Test;
import org.junit.Ignore;

import fortress.data.PersistentSet;
import fortress.data.PersistentHashSet;
import fortress.data.PersistentInsertionOrderedHashSet;
import java.util.Set;
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import cyclops.data.BankersQueue;
import com.oath.cyclops.types.persistent.PersistentQueue;

public class PersistentInsertionOrderedHashSetTest {
    
    @Test
    public void equalityWithSets() {
        PersistentSet<Integer> s1 = PersistentInsertionOrderedHashSet.empty();
        PersistentSet<Integer> s2 = s1.plus(5);
        PersistentSet<Integer> s3 = s2.plusAll(List.of(6, 5, 6, 7, 8));
        
        assertTrue(Set.of().equals(s1));
        assertTrue(s1.equals(Set.of()));
        
        assertTrue(Set.of(5).equals(s2));
        assertTrue(s2.equals(Set.of(5)));
        
        assertTrue(Set.of(5, 6, 7, 8).equals(s3));
        assertTrue(s3.equals(Set.of(5, 6, 7, 8)));
    }
    
    @Test
    public void insertionOrdered() {
        // PersistentQueue<String> q = BankersQueue.<String>empty()
        //     .plus("cat")
        //     .plus("dog")
        //     .plus("mouse")
        //     .plus("rat")
        //     .plus("raccoon")
        //     .plus("bird");
        // List<String> lll = new ArrayList<>();
        // for(String s : q) {
        //     lll.add(s);
        // }
        // assertEquals(List.of(), lll);
        
        PersistentSet<String> s1 = PersistentInsertionOrderedHashSet.empty();
        s1 = s1.plus("cat");
        s1 = s1.plus("dog");
        s1 = s1.plus("mouse");
        s1 = s1.plus("rat");
        s1 = s1.plus("raccoon");
        s1 = s1.plus("bird");
        
        Iterator<String> iter = s1.iterator();
        assertEquals(iter.next(), "cat");
        assertEquals(iter.next(), "dog");
        assertEquals(iter.next(), "mouse");
        assertEquals(iter.next(), "rat");
        assertEquals(iter.next(), "raccoon");
        assertEquals(iter.next(), "bird");
        
        PersistentSet<String> s2 = PersistentHashSet.empty();
        s2 = s2.plus("cat");
        s2 = s2.plus("dog");
        s2 = s2.plus("mouse");
        s2 = s2.plus("rat");
        s2 = s2.plus("raccoon");
        s2 = s2.plus("bird");
        
        List<String> l1 = new ArrayList<>(s1);
        List<String> l2 = new ArrayList<>(s2);
        
        assertEquals(l1, List.of("cat", "dog", "mouse", "rat", "raccoon", "bird"));
        assertNotEquals(l1, l2); // Otherwise we aren't actually testing anything
    }
}
