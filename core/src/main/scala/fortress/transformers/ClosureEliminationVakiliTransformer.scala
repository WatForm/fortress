package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.ClosureEliminator
import fortress.operations.ClosureEliminatorVakili
import fortress.problemstate._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.transformers._
import fortress.data.IntSuffixNameGenerator
import fortress.operations.RecursiveAccumulator

// This does not function like a full Closure Elimination Transformer
object ClosureEliminationVakiliTransformer extends ProblemStateTransformer {
    // ASSUMES the problem state is in NNF
    def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {
            // Collect names we can't generate as they are already used
            val forbiddenNames = scala.collection.mutable.Set[String]()
            
            for(sort <- theory.sorts) {
                forbiddenNames += sort.name
            }
            
            for(fdecl <- theory.functionDeclarations) {
                forbiddenNames += fdecl.name
            }
            
            for(constant <- theory.constants) {
                forbiddenNames += constant.name
            }

            val nameGenerator = new IntSuffixNameGenerator(forbiddenNames.toSet, 0)

            // We cannot replace relations that ever have a positive closure
            val allRelations = theory.functionDeclarations.map(fdec => {fdec.name})
            var allowedRelations = allRelations.toSet
            for (axiom <- theory.axioms){
                val nonNegativelyClosed = RecursiveAccumulator.nonNegativeClosures(axiom)
                allowedRelations --= nonNegativelyClosed
            }

            // Remove the allowed closures
            val closureFunctions = scala.collection.mutable.Set[FuncDecl]()
            var resultTheory = theory.withoutAxioms

            for (axiom <- theory.axioms){
                val eliminator = new ClosureEliminatorVakili(axiom, allowedRelations.toSet, resultTheory.signature, scopes, nameGenerator)
                val newAxiom = eliminator.convert()
                resultTheory = resultTheory.withFunctionDeclarations(eliminator.getClosureFunctions)
                closureFunctions ++= eliminator.getClosureFunctions
                resultTheory = resultTheory.withAxioms(eliminator.getClosureAxioms)
                resultTheory = resultTheory.withAxiom(newAxiom)
            }


            // Remove the added functions
            def unapply(interp: Interpretation) = {
                interp.withoutFunctions(closureFunctions.toSet)
            }
            
            ProblemState(resultTheory, scopes, skc, skf, rangeRestricts, unapplyInterp :+ unapply, distinctConstants)
        }
    }
    override def name: String = "Closure Elimination Vakili Transformer"
}