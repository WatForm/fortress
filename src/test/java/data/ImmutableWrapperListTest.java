import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;
import org.junit.Test;
import org.junit.Ignore;

import fortress.data.ImmutableList;
import fortress.data.ImmutableWrapperList;
import java.util.List;

public class ImmutableWrapperListTest {
    @Test
    public void equality() {
        List<Integer> l1 = List.of(1, 2);
        List<Integer> l2 = List.of(1, 2);
        List<Integer> l3 = List.of(1, 3);
        ImmutableList<Integer> il1 = ImmutableWrapperList.copyCollection(l1);
        ImmutableList<Integer> il2 = ImmutableWrapperList.copyCollection(l2);
        ImmutableList<Integer> il3 = ImmutableWrapperList.copyCollection(l3);
        
        assertTrue(il1.equals(il2));
        assertTrue(il2.equals(il1));
        
        assertFalse(il1.equals(il3));
        assertFalse(il3.equals(il1));
        
        assertFalse(il3.equals(il2));
        assertFalse(il2.equals(il3));
    }
}
