package fortress.operations

import fortress.msfol._
import fortress.operations.TermMetrics.termCount
import fortress.operations.TheoryOps._
import fortress.operations.TermOps._

import scala.annotation.tailrec
import scala.collection.mutable

trait DefinitionInlineHeuristic {
    def shouldInline(defn: FunctionDefinition, args: Seq[Term]): Boolean
}

/**
  * A heuristic that inlines when the size of the inlined term, after simplifying, is "significantly" smaller than
  * the definition's body.
  */
class SizeAfterSimplifyingHeuristic(proportion: Double, theory: Theory) extends DefinitionInlineHeuristic {
    override def shouldInline(defn: FunctionDefinition, args: Seq[Term]): Boolean = {
//         termCount(simplify(DefinitionInliner.doInline(defn, args), theory)) < proportion * termCount(defn.body)
        val originalCount = termCount(defn.body)
        val simplifyCount = termCount(simplify(DefinitionInliner.doInline(defn, args), theory))
//        println(s"original = ${defn.body}")
//        println(s"simplified = ${simplify(DefinitionInliner.doInline(defn, args), theory)}")
        println(s"original: $originalCount, simplified: $simplifyCount (threshold: ${proportion * originalCount})")
        simplifyCount < proportion * originalCount
    }

    private def simplify(term: Term, theory: Theory): Term =
        DefinitionInliner.inlineTerm(term.simplify, theory, this).simplify
}

/**
  * A heuristic that inlines when any of the arguments are constant (i.e. has the Value trait).
  */
object AnyConstantArgsHeuristic extends DefinitionInlineHeuristic {
    override def shouldInline(defn: FunctionDefinition, args: Seq[Term]): Boolean = {
//        println(s"defn = ${defn.name}, args = $args, should inline = ${args exists (_.isInstanceOf[Value])}")
        args exists (_.isInstanceOf[Value])
    }
}

/**
  * A heuristic that inlines when all of the arguments are constant (i.e. has the Value trait).
  */
object AllConstantArgsHeuristic extends DefinitionInlineHeuristic {
    override def shouldInline(defn: FunctionDefinition, args: Seq[Term]): Boolean =
        args forall (_.isInstanceOf[Value])
}

/**
  * A heuristic that inlines if the definition call is independent with respect to the theory, i.e. it can be fully
  * computed (and presumably simplified) statically.
  * This means that it does not reference any function declarations or constant declarations and its arguments are
  * values.
  */
class InterpretationIndependentHeuristic(theory: Theory) extends DefinitionInlineHeuristic {

    private val interpIndependentConstDefns = mutable.Set[String]()
    private val interpIndependentFuncDefns = mutable.Set[String]()

    private object IsInterpIndependent extends NaturalReduction[Boolean](true, (a, b) => a && b) {
        override val exceptionalMappings: PartialFunction[Term, Boolean] = {
            case App(functionName, args) => args.map(naturalRecur).forall(b => b) &&
                // Declared functions are not independent, so all apps must be to independent definitions
                theory.functionDefinitions.exists(_.name == functionName) &&
                (interpIndependentFuncDefns contains functionName)
            case Var(name) =>
                // Declared constants are not independent and all defined constants must be independent
                // TODO: What if this is a bound variable or definition parameter shadowing a constant?
                !theory.constantDeclarations.exists(_.name == name) &&
                    (!theory.constantDefinitions.exists(_.name == name) || (interpIndependentConstDefns contains name))
        }
    }

    for (defn <- theory.signature.definitionsInDependencyOrder()) defn match {
        case Left(cDef) =>
            if (IsInterpIndependent.naturalRecur(cDef.body))
                interpIndependentConstDefns += cDef.name
        case Right(fDef) =>
            if (IsInterpIndependent.naturalRecur(fDef.body))
                interpIndependentFuncDefns += fDef.name
    }

    override def shouldInline(defn: FunctionDefinition, args: Seq[Term]): Boolean = {
        val result = (interpIndependentFuncDefns contains defn.name) && (args forall (_.isInstanceOf[Value]))
//        if (result) println(s"inlining: ${defn.name}")
//        else println(s"not inlining: ${defn.name}")
        result
    }
}

// Heuristic ideas:
// - only expression-valued (non-BoolSort)?
// - only lookup tables?
// what we want is something that "significantly simplifies"...

// how about: all of
// - has no references to functions or constants
// - args are domain elements
// ie. constant-valued wrt the theory

/** Inline some definitions based on a heuristic. */
object DefinitionInliner {

//    private def addMaps[A](map1: Map[A, Int], map2: Map[A, Int]): Map[A, Int] = {
//        val commonKeys = map1.keySet intersect map2.keySet
//        (map1 -- commonKeys) ++ (map2 -- commonKeys) ++ (
//            for (key <- commonKeys)
//                yield key -> (map1(key) + map2(key))
//        )
//    }
//
//    private object CountUsages extends NaturalReduction[Map[String, Int]](Map.empty, addMaps[String]) {
//        override val exceptionalMappings: PartialFunction[Term, Map[String, Int]] = {
//            case App(funcName, _) =>
//                if (theory.functionDefinitions.exists(_.name == funcName)) Map(funcName -> 1)
//                else Map.empty
//        }
//    }
//
//    private lazy val defnUsageCounts: Map[String, Int] =
//        theory.allTerms map (CountUsages.naturalRecur(_)) reduce addMaps[String]

    def doInline(defn: FunctionDefinition, args: Seq[Term]): Term = {
        // TODO fastSubstitute requires no quantifiers - ensure this
        defn.body.fastSubstitute(((defn.argSortedVar map (_.variable)) zip args).toMap).simplify
//        var term = defn.body
//        for ((param, arg) <- defn.argSortedVar zip args) {
//            term = term.substitute(param.variable, arg)
//        }
//        term.simplify
    }

    private class Inliner(theory: Theory, heuristic: DefinitionInlineHeuristic) extends NaturalTermRecursion {
        var didInline = false

        private val cache = mutable.Map[(String, Seq[Term]), Term]()

        override val exceptionalMappings: PartialFunction[Term, Term] = {
            case app @ App(funcName, args) =>
                val newArgs = args.map(naturalRecur)
                theory.functionDefinitions find (_.name == funcName) match {
                    case Some(defn) =>
                        if (heuristic.shouldInline(defn, newArgs)) {
                            didInline = true
                            cache.getOrElseUpdate((defn.name, newArgs), {
                                println(s"not cached: ${defn.name}($newArgs)")
                                doInline(defn, newArgs)
                            })
                        }
                        else app
                    case None => app
                }
        }
    }

    var numRecursions = 0

    @tailrec
    def inline(theory: Theory, heuristic: DefinitionInlineHeuristic): Theory = {
        // run inliner until fixpoint
//        println(s"Inline is recursing: $theory")
        numRecursions += 1
        println(s"recursion #$numRecursions")
        val inliner = new Inliner(theory, heuristic)
        val newTheory = theory.mapAllTerms(inliner.naturalRecur)

//        var newSignature = theory.signature
//        for (defn <- theory.signature.definitionsInDependencyOrder().reverse) defn match {
//            case Left(cDef) =>
//                newSignature = newSignature.withoutConstantDefinition(cDef)
//                val newBody = inliner.naturalRecur(cDef.body)
//                newSignature = newSignature.withConstantDefinition(cDef.copy(body = newBody))
//            case Right(fDef) =>
//                newSignature = newSignature.withoutFunctionDefinition(fDef)
//                val newBody = inliner.naturalRecur(fDef.body)
//                newSignature = newSignature.withFunctionDefinition(fDef.copy(body = newBody))
//        }
//        val newAxioms = theory.axioms map inliner.naturalRecur
//        val newTheory = theory.copy(signature = newSignature, axioms = newAxioms)

        if (inliner.didInline) inline(newTheory, heuristic)
        else newTheory
    }

    @tailrec
    def inlineTerm(term: Term, theory: Theory, heuristic: DefinitionInlineHeuristic): Term = {
        val inliner = new Inliner(theory, heuristic)
        val newTerm = inliner.naturalRecur(term)
        if (inliner.didInline) inlineTerm(newTerm, theory, heuristic)
        else newTerm
    }

}
