package fortress.transformers

import fortress.msfol._
import fortress.operations._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._

object SimplifyWithScalarQuantifiersTransformer extends TheoryTransformer {
    override def apply(theory: Theory): Theory = theory
        .mapAxioms(_.simplify)  // necessary before ScalarQuantifierSimplifier
        .mapAxioms(ScalarQuantifierSimplifier.simplify)
        .mapAxioms(_.simplify)  // clean up anything introduced

    override def name: String = "Simplify Scalar Quantifiers Transformer"
}
