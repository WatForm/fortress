package fortress.transformers

import fortress.msfol._
import fortress.operations._
import fortress.operations.TheoryOps._

/** Applies a simplification to the formulas in a theory, replacing them with equivalent formulas.
  * All other aspects of the theory remain unchanged.
  *
  * This variant removes the simplification of equality formulas between two domain constants
  * using the fact that the the domain constants were not equal. As in the "collapsing constants"
  * approach for solving with non-exact scope, constants are no longer distinct.
  * */

//Fortress previously was able to use the fact that the domain constants were not equal to immediately simplify equality formulas between two domain constants. Obviously, this simplification needed to be removed.
class SimplifyTransformer2 extends TheoryTransformer {
    
    override def apply(theory: Theory): Theory =  theory.mapAxioms(Simplifier2.simplify)
    
    override def name: String = "Simplify Transformer 2"
}
