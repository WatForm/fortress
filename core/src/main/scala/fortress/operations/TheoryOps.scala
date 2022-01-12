package fortress.operations

import fortress.msfol._
import fortress.data._

import scala.language.implicitConversions
import fortress.interpretation._
import fortress.operations.TermMetrics._
import fortress.sortinference._

import scala.collection.mutable

case class TheoryOps private(theory: Theory) {
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

    // Returns the maximum arity of functions of a theory
    def maxFunctionArity: Int = {
        if (functionCount > 0) {
            theory.functionDeclarations.map(_.arity).max
        } else {
            0
        }
    }

    // Counts the number of function args that are of boolean sort
    def boolArgCount: Int = {
        theory.functionDeclarations.map(_.argSorts.count(_ == BoolSort)).sum
    }

    // Returns the number of terms in a theory
    def termCount: Int = {
        theory.axioms.toList.map(TermMetrics.termCount).sum
    }

    // Returns depth of quantification of a theory
    def depthQuantification: Int = {
        theory.axioms.map(TermMetrics.depthQuantification).max
    }

    // Returns depth of nested functions of a theory
    def depthNestedFunc: Int = {
        theory.axioms.map(TermMetrics.depthNestedFunc).max
    }

    // Returns the number of sorts created by Sort Inference
    def inferSortsCount: Int = {
        inferSorts._1.sorts.size - sortCount
    }

    // Returns whether sort inference found any new sorts
    def newSortsInferred: Boolean = {
        inferSortsCount > 0
    }

    // Returns whether sort inference found any new sorts
    def mostUsedDeclarations: Map[Declaration, Int] = {
        val helper = (r: mutable.Map[Declaration, Int], i: Declaration) => r + (i -> 0)
        val profilingInfo = (theory.constants ++ theory.functionDeclarations).foldLeft(mutable.Map.empty[Declaration, Int])(helper)
        theory.axioms.foreach(axiom => TermMetrics.declarationCountMap(axiom, profilingInfo))
        profilingInfo.toMap
    }
}

object TheoryOps {
    implicit def wrapTheory(theory: Theory): TheoryOps = TheoryOps(theory)
}
