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

    // Returns the number of sorts
    def sortCount: Int = {
        theory.sorts.size
    }

    // Returns the number of function declarations
    def functionCount: Int = {
        theory.functionDeclarations.size
    }

    // Returns the number of predicates
    def predicateCount: Int = {
        theory.functionDeclarations.count(_.resultSort == BoolSort)
    }

    // Returns depth of quantification of a term
    def depthQuantification(term: Term): Int = term match {
        case Forall(_, body) => depthQuantification(body) + 1
        case Exists(_, body) => depthQuantification(body) + 1
        case AndList(args) => args.map(depthQuantification).max
        case OrList(args) => args.map(depthQuantification).max
        case Top | Bottom | Var(_) | EnumValue(_) => 0;
        case Not(body) => depthQuantification(body)
        case Distinct(args) => args.map(depthQuantification).max
        case Implication(p, q) => List(depthQuantification(p), depthQuantification(q)).max
        case Iff(p, q) => List(depthQuantification(p), depthQuantification(q)).max
        case Eq(p, q) => List(depthQuantification(p), depthQuantification(q)).max
        case App(_, args) => args.map(depthQuantification).max
        case BuiltinApp(_, _) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => 0
    }

    // Returns depth of quantification of a theory
    def depthQuantification: Int = {
        theory.axioms.map(depthQuantification).max
    }

    // Returns depth of nested functions of a term
    def depthNestedFunc(term: Term): Int = term match {
        case Forall(_, body) => depthNestedFunc(body)
        case Exists(_, body) => depthNestedFunc(body)
        case AndList(args) => args.map(depthNestedFunc).max
        case OrList(args) => args.map(depthNestedFunc).max
        case Top | Bottom | Var(_) | EnumValue(_) => 0;
        case Not(body) => depthNestedFunc(body)
        case Distinct(args) => args.map(depthNestedFunc).max
        case Implication(p, q) => List(depthNestedFunc(p), depthNestedFunc(q)).max
        case Iff(p, q) => List(depthNestedFunc(p), depthNestedFunc(q)).max
        case Eq(p, q) => List(depthNestedFunc(p), depthNestedFunc(q)).max
        case App(_, args) => args.map(depthNestedFunc).max + 1
        case BuiltinApp(_, _) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => 0
    }

    // Returns depth of nested functions of a theory
    def depthNestedFunc: Int = {
        theory.axioms.map(depthNestedFunc).max
    }
}

object TheoryOps {
    implicit def wrapTheory(theory: Theory): TheoryOps = TheoryOps(theory)
}
