package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.Skolemization
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.interpretation.Interpretation
import fortress.problemstate.ProblemState
import fortress.util.Errors

/** Skolemizes existential quantifiers in the theory.
  * Requires that the theory be in negation normal form.
  */
object SkolemizeTransformer extends ProblemStateTransformer {
    
    override def name: String = "Skolemize Transformer"

    override def apply(problemState: ProblemState): ProblemState = {

        // Skolemize can be applied to a problem with ites - it just won't skolemize the condition
        // of an ite because in one case it is true and the other branch it is false

        // as much iflifting as possible
        if (problemState.flags.haveRunIfLifting==false ) {
            println(s"WARNING: IfLifting Transformer should be run before Skolemization")
        } 
        // must have done as much nnf as possible
        if (problemState.flags.haveRunNNF==false ) {
            // TODO: 
            println(s"WARNING: NNF Transformer should be run before Skolemization")
        }
       
        val theory = problemState.theory
        
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

        for(cDef <- theory.constantDefinitions){
            forbiddenNames += cDef.name
        }

        for(fDef <- theory.functionDefinitions){
            forbiddenNames += fDef.name
        }
        
        // TODO: do we need this restriction if Substituter already restricts these inside one term?
        for(axiom <- theory.axioms) {
            forbiddenNames ++= axiom.allSymbols
        }
        
        val nameGenerator = new IntSuffixNameGenerator(forbiddenNames.toSet, 0)
        
        var resultTheory = theory.withoutAxioms
        val newSkolemConstants = scala.collection.mutable.Set.empty[AnnotatedVar]
        val newSkolemFunctions = scala.collection.mutable.Set.empty[FuncDecl]
        def updateWithResult(skolemResult: Skolemization.SkolemResult): Unit = {
            newSkolemConstants ++= skolemResult.skolemConstants
            newSkolemFunctions ++= skolemResult.skolemFunctions
            resultTheory = resultTheory.withFunctionDeclarations(skolemResult.skolemFunctions.toList)
            resultTheory = resultTheory.withConstantDeclarations(skolemResult.skolemConstants.toList)
        }

        for(axiom <- theory.axioms) {
            val skolemResult = Skolemization.skolemize(axiom, resultTheory.signature, nameGenerator)
            val newAxiom = skolemResult.skolemizedTerm
            updateWithResult(skolemResult)
            resultTheory = resultTheory.withAxiom(newAxiom)
        }

        /* 2024-04-10 Decided we can't skolemize function/constant bodies because we don't know if 
           they will be used in a positive or negative context

        Leftover comments:
        // We can skolemize in definitions because skolemization only cares about the free variables IN THE TERM
        // First-Order Logic and Automated Theorem Proving 2nd ed., Melvin Fitting p. 206
        // Function definitions can be skolemized as if each argument was universally quantified
        val functionDefinitions = resultTheory.functionDefinitions
        //resultTheory = resultTheory.withoutFunctionDefinitions
        for (fDef <- theory.functionDefinitions) {
            resultTheory = resultTheory.withoutFunctionDefinition(fDef)
            val wrappedTerm = Forall(fDef.argSortedVar, fDef.body)
            val skolemResult = Skolemization.skolemize(wrappedTerm, resultTheory.signature, nameGenerator)
            updateWithResult(skolemResult)
            
            // unfold the result term to make the new axiom
            skolemResult.skolemizedTerm match {
                case Forall(_, newBody) => {
                    val newDef = FunctionDefinition(fDef.name, fDef.argSortedVar, fDef.resultSort, newBody)
                    resultTheory = resultTheory.withFunctionDefinition(newDef) 
                }
                case _ => Errors.Internal.impossibleState("Skolemization of Forall did not return Forall.")
            }
        }
        //resultTheory = resultTheory.withoutConstantDefinitions
        for (cDef <- theory.constantDefinitions){
            resultTheory = resultTheory.withoutConstantDefinition(cDef)
            val skolemResult = Skolemization.skolemize(cDef.body, resultTheory.signature, nameGenerator)
            updateWithResult(skolemResult)
            resultTheory = resultTheory.withConstantDefinition(
                ConstantDefinition(
                    cDef.avar,
                    skolemResult.skolemizedTerm
                )
            )
        }
        */

        
        val unapply: Interpretation => Interpretation = {
            interp => interp.withoutConstants(newSkolemConstants.toSet).withoutFunctions(newSkolemFunctions.toSet)
        }
        /*
        ProblemState(
            resultTheory,
            scopes, skc ++ newSkolemConstants.toSet,
            skf ++ newSkolemFunctions.toSet,
            rangeRestricts,
            unapply :: unapplyInterp,
            distinctConstants
        )
        */
        problemState.copy(
            theory = resultTheory,
            skolemConstants = problemState.skolemConstants ++ newSkolemConstants.toSet,
            skolemFunctions = problemState.skolemFunctions ++ newSkolemFunctions.toSet,
            unapplyInterp = unapply :: problemState.unapplyInterp,
            flags = problemState.flags.copy(haveRunSkolemizer = true)
        )
    }
    
    
    
}
