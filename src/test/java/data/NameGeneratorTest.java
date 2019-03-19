import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import org.junit.Test;
import org.junit.Ignore;

import fortress.data.NameGenerator;
import fortress.data.SubIntNameGenerator;
import java.util.Set;

public class NameGeneratorTest {
    @Test
    public void SubIntTest() {
        Set<String> forbid = Set.of("sk_1");
        SubIntNameGenerator gen = new SubIntNameGenerator(forbid, 0);
        assertEquals("sk_0", gen.freshName("sk"));
        assertEquals("sk_2", gen.freshName("sk"));
        assertEquals("sk_3", gen.freshName("sk"));
    }
}
