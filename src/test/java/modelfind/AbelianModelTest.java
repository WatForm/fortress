import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import org.junit.Test;
import org.junit.BeforeClass;
import org.junit.Ignore;

import fortress.tfol.*;
import fortress.modelfind.*;
import java.util.List;
import java.util.ArrayList;
import java.io.*;
import fortress.util.Errors;

public class AbelianModelTest {
    
    // Just test z3 Java API can be properly called and used
    
    @Test
    public void foobar() {
        Z3TestDummy dummy = new Z3TestDummy();
    }
    
    
    // @Test
    // public void foo() {
    //     Theory nonAbelianGroupTheory3 = Theories.makeNonAbelianGroupTheory();
    //     nonAbelianGroupTheory3.addScope(Theories.groupType, 3);
    //     new NaiveScopeTransformer().transformTheory(nonAbelianGroupTheory3);
    //     assertNull(nonAbelianGroupTheory3.toString());
    // 
    // }
    // @Test
    // public void nonAbelianGroup3() {
    //     // There does not exist a nonabelian group of size 3
    //     Theory nonAbelianGroupTheory3 = Theories.makeNonAbelianGroupTheory();
    //     nonAbelianGroupTheory3.addScope(Theories.groupType, 3);
    // 
    //     ModelFinder modelFinder = new ModelFinder(
    //         new NaiveScopeTransformer(),
    //         new Z3CommandLine()
    //     );
    // 
    //     ModelFinder.Result size5Result = modelFinder.findModel(nonAbelianGroupTheory3, 1000);
    //     assertEquals(nonAbelianGroupTheory3.toString(), ModelFinder.Result.UNSAT, size5Result);  
    // }
    // 
    // @Test
    // public void nonAbelianGroup6() {
    //     // There does exist a nonabelian group of size 6
    //     Theory nonAbelianGroupTheory6 = Theories.makeNonAbelianGroupTheory();
    //     nonAbelianGroupTheory6.addScope(Theories.groupType, 6);
    // 
    //     ModelFinder modelFinder = new ModelFinder(
    //         new NaiveScopeTransformer(),
    //         new Z3CommandLine()
    //     );
    // 
    //     ModelFinder.Result size6Result = modelFinder.findModel(nonAbelianGroupTheory6, 1000);
    //     assertEquals(nonAbelianGroupTheory6.toString(), ModelFinder.Result.SAT, size6Result);
    // }
}
