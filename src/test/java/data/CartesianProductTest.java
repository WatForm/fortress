import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;
import org.junit.Test;
import org.junit.Ignore;

import fortress.data.CartesianProduct;
import java.util.List;
import java.util.Iterator;

public class CartesianProductTest {
    @Test
    public void iteration() {
        List<Integer> l1 = List.of(1, 2, 3);
        List<Integer> l2 = List.of(4, 5);
        List<Integer> l3 = List.of(6);
        List<Integer> l4 = List.of(7, 8);
        
        CartesianProduct<Integer> product = new CartesianProduct<>(List.of(l1, l2, l3, l4));
        
        Iterator<List<Integer>> iterator = product.iterator();
        assertTrue(iterator.hasNext());
        assertEquals(List.of(1, 4, 6, 7), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(2, 4, 6, 7), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(3, 4, 6, 7), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(1, 5, 6, 7), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(2, 5, 6, 7), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(3, 5, 6, 7), iterator.next());
        assertTrue(iterator.hasNext());
        
        assertEquals(List.of(1, 4, 6, 8), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(2, 4, 6, 8), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(3, 4, 6, 8), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(1, 5, 6, 8), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(2, 5, 6, 8), iterator.next());
        assertTrue(iterator.hasNext());
        assertEquals(List.of(3, 5, 6, 8), iterator.next());
        assertFalse(iterator.hasNext());
    }
}
