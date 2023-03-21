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
import fortress.operations.NormalForms

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
            
            for(constant <- theory.constantDeclarations) {
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
            // TODO We conservatively do not allow this to elim clopsure in definitions
            for (cDef <- theory.signature.constantDefinitions) {
                allowedRelations --= RecursiveAccumulator.allClosures(cDef.body)
            }

            for (fDef <- theory.signature.functionDefinitions) {
                allowedRelations --= RecursiveAccumulator.allClosures(fDef.body)
            }

            // Remove the allowed closures
            val closureFunctions = scala.collection.mutable.Set[FuncDecl]()
            var resultTheory = theory.withoutAxioms
            
            /** Updates the resultTheory with values from the closureEliminator after it runs its conversion
             * Notably, no auxilary functions
             */
            def updateResult(closureEliminator: ClosureEliminator): Unit = {
                resultTheory = resultTheory.withFunctionDeclarations(closureEliminator.getClosureFunctions)
                closureFunctions ++= closureEliminator.getClosureFunctions
                // New axioms must be in negation normal form
                resultTheory = resultTheory.withAxioms(closureEliminator.getClosureAxioms.map(NormalForms.nnf))
            }
            for (axiom <- theory.axioms){
                val eliminator = new ClosureEliminatorVakili(axiom, allowedRelations.toSet, resultTheory.signature, scopes, nameGenerator)
                // Ensure NNF
                val newAxiom = NormalForms.nnf(eliminator.convert())
                resultTheory = resultTheory.withFunctionDeclarations(eliminator.getClosureFunctions)
                closureFunctions ++= eliminator.getClosureFunctions
                // Axioms in NNF
                resultTheory = resultTheory.withAxioms(eliminator.getClosureAxioms.map(NormalForms.nnf))
                resultTheory = resultTheory.withAxiom(newAxiom)
            }

            for (cDef <- theory.signature.constantDefinitions) {
                val body = cDef.body
                // we do not support recursive definitions yet
                resultTheory = resultTheory withoutConstantDefinition cDef
                val closureEliminator = new ClosureEliminatorVakili(body, allowedRelations.toSet, resultTheory.signature, scopes, nameGenerator)
                // ensure nnf 
                val newBody = NormalForms.nnf(closureEliminator.convert())
                updateResult(closureEliminator)
                resultTheory = resultTheory.withConstantDefinition(ConstantDefinition(cDef.avar, newBody))
            }

            for (fDef <- theory.signature.functionDefinitions) {
                val body = fDef.body
                // we do not support recursive definitions yet
                resultTheory = resultTheory withoutFunctionDefinition fDef
                val closureEliminator = new ClosureEliminatorVakili(body, allowedRelations.toSet, resultTheory.signature, scopes, nameGenerator)
                // ensure nnf 
                val newBody = NormalForms.nnf(closureEliminator.convert())
                updateResult(closureEliminator)
                val newFDef = fDef.copy(body = newBody)
                resultTheory = resultTheory.withFunctionDefinition(newFDef)
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