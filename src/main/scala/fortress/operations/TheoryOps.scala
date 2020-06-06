package fortress.operations

import fortress.msfol._
import fortress.data._
import scala.language.implicitConversions
import fortress.interpretation._

case class TheoryOps private (theory: Theory) {
    def mapAxioms(f: Term => Term) = Theory(theory.signature, theory.axioms map f)
    
    def verifyInterpretation(interpretation: Interpretation): Boolean =
        new InterpretationVerifier(theory).verifyInterpretation(interpretation)
    
    def withoutAxioms: Theory = Theory(theory.signature, Set.empty)
}

object TheoryOps {
    implicit def wrapTheory(theory: Theory): TheoryOps = TheoryOps(theory)
}
