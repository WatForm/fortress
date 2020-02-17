import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.util.StopWatch;

public class StopWatchTest {
    @Test
    public void formatMilliseconds() {
        assertEquals("0.043s", StopWatch.formatNano(43000000L));
    }
    
    @Test
    public void formatSeconds() {
        assertEquals("54.321s", StopWatch.formatNano(54321000000L));
    }
    
    @Test
    public void formatMinutes() {
        assertEquals("10m 54.321s", StopWatch.formatNano(654321000000L));
    }
    
    @Test
    public void formatHours() {
        assertEquals("21h 15m 43.210s", StopWatch.formatNano(76543210000000L));
    }
}
