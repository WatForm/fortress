import static org.junit.Assert.assertEquals;
import org.junit.Test;
import fortress.fol.*;
import fortress.lambda.*;
import fortress.fol.pterm.*;

public class SimpleTest {

  @Test
  public void firstTest() {
      PTerm type = new PVar("A");
      Term v = new Var("v", type);
      assertEquals(6, 6);
  }
}