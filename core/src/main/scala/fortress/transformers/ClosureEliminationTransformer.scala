package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.ClosureEliminator
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.problemstate._
import fortress.operations.NormalForms

/** Replaces transitive closure terms with a term representing the application of a new relation
 but with same arguments. **/
trait ClosureEliminationTransformer extends ProblemStateTransformer {
    // This is basically a wrapper function so we can override just this and not all of apply
    // need to make this abstract
    def buildEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator): ClosureEliminator

    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes
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
        
        var resultTheory = theory.withoutAxioms

        // TODO can we make the elimiator only once?
        val closureFunctions = scala.collection.mutable.Set[FuncDecl]()
        val auxilaryFunctions = scala.collection.mutable.Set[FuncDecl]()

        /** Updates the resultTheory with values from the closureEliminator after it runs its conversion
        */
        def updateResult(closureEliminator: ClosureEliminator): Unit = {
            resultTheory = resultTheory.withFunctionDeclarations(closureEliminator.getClosureFunctions)
            closureFunctions ++= closureEliminator.getClosureFunctions
            resultTheory = resultTheory.withFunctionDeclarations(closureEliminator.getAuxilaryFunctions)
            auxilaryFunctions ++= closureEliminator.getAuxilaryFunctions
            // New axioms must be in negation normal form
            resultTheory = resultTheory.withAxioms(closureEliminator.getClosureAxioms.map(NormalForms.nnf))
        }
        for(axiom <- theory.axioms) {
            val closureEliminator = buildEliminator(axiom, resultTheory.signature, scopes, nameGenerator)
            // ensure nnf
            val newAxiom = NormalForms.nnf(closureEliminator.convert())
            updateResult(closureEliminator)
            resultTheory = resultTheory.withAxiom(newAxiom)
        }

        // We keep everything in the theory until we replace it so any dependencies are still there
        for (cDef <- theory.signature.constantDefinitions) {
            val body = cDef.body
            // we do not support recursive definitions yet
            resultTheory = resultTheory withoutConstantDefinition cDef
            val closureEliminator = buildEliminator(body, resultTheory.signature, scopes, nameGenerator)
            // ensure nnf 
            val newBody = NormalForms.nnf(closureEliminator.convert())
            updateResult(closureEliminator)
            resultTheory = resultTheory.withConstantDefinition(ConstantDefinition(cDef.avar, newBody))
        }

        for (fDef <- theory.signature.functionDefinitions) {
            val body = fDef.body
            // we do not support recursive definitions yet
            resultTheory = resultTheory withoutFunctionDefinition fDef
            val closureEliminator = buildEliminator(body, resultTheory.signature, scopes, nameGenerator)
            // ensure nnf 
            val newBody = NormalForms.nnf(closureEliminator.convert())
            updateResult(closureEliminator)
            val newFDef = fDef.copy(body = newBody)
            resultTheory = resultTheory.withFunctionDefinition(newFDef)
        }



        // Remove the added functions
        def unapply(interp: Interpretation) = {
            interp.withoutFunctions(closureFunctions.toSet).withoutFunctions(auxilaryFunctions.toSet)
        }
        
        problemState.copy(
            theory=resultTheory,
            unapplyInterp = problemState.unapplyInterp :+ unapply
        )
    }
    
    override def name: String = "Closure Elimination Abstract"
    
}

