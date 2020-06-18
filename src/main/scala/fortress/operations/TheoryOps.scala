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
    
    def smtlib: String = {
        val writer = new java.io.StringWriter
        val converter = new SmtlibConverter(writer)
        converter.writeTheory(theory)
        writer.toString
    }
    
    def inferSorts: (Theory, SortSubstitution) = SortInference.inferSorts(theory)
}

object TheoryOps {
    implicit def wrapTheory(theory: Theory): TheoryOps = TheoryOps(theory)
}
