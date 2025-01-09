package fortress.transformers

import scala.collection.mutable

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.operations._
import fortress.util.Errors
import fortress.problemstate.ProblemState
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator

/** Type-checks a theory, and performs sanitization (for example, replacing Equals of booleans with Iff).
  * Throws an exception if the theory does not type-check correctly.
  */
object TypecheckSanitizeTransformer extends ProblemStateTransformer {

    // Note that a formula will not typecheck if it has any free variables (that are not constants of the signature)

    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        var containsItes = false
        var containsExists = false

        def checkResult(result:TypeCheckResult, s:Sort):Term = {
            containsItes = containsItes || result.containsItes
            containsExists = containsExists || result.containsExists
            // System.out.println(axiom.toString + (result.sort).toString) ;
            if (result.sort != s) 
                // This error message isn't great because typechecking does change
                // some parts of the term such as ites over Booleans
                Errors.Internal.preconditionFailed(s"typechecking of "+result.sanitizedTerm.toString + " had sort "+ result.sort.toString + "when it should be "+s)
            return result.sanitizedTerm            
        }        
        var newTheory = theory.mapAxioms(
                t => checkResult(t.typeCheck(theory.signature), BoolSort))

        // There is nothing to stop recursive definitions
        for(cDef <- theory.signature.constantDefinitions){
            newTheory = newTheory.withoutConstantDefinition(cDef)
            newTheory = newTheory.withConstantDefinition(
                cDef.mapBody(b => 
                    checkResult(cDef.body.typeCheck(theory.signature),cDef.sort)))
        }

        // We must ensure that names are not used for arguments in function definitions
        // This is a stopgap and could potentially be replaced with proper scoping in the future
        // SMTLIB sees a unique id as IDxType. Since our substitution would not detect
        // namexA vs namexB we only include function names, which must have at least one argument
        // Therefore they cannot share a type with the parameter variable
        val forbiddenNames = mutable.Set.empty[String]
        forbiddenNames ++= theory.functionDefinitions.map(_.name)
        forbiddenNames ++= theory.functionDeclarations.map(_.name)
        
        // The name generator forbids any name it "adds", so we need to refresh for every argument
        for(fDef <- theory.signature.functionDefinitions){
            newTheory = newTheory.withoutFunctionDefinition(fDef)

            val nameGen = new IntSuffixNameGenerator(forbiddenNames.toSet, 0)
            // If the parameter name is "taken" by a definition, use a fresh name
            // If we use a fresh name, we need to substitute it!
            var substitutions = mutable.Map.empty[Var, Term]
            val newAvars: Seq[AnnotatedVar] = fDef.argSortedVar.map(avar => {
                val originalName = avar.name
                val newName = nameGen.freshName(originalName)

                if (newName != originalName){
                    substitutions.addOne(avar.variable -> Var(newName))
                }
                
                // Only change the name
                avar.copy(variable=Var(newName))
            })

            var newBody = if (substitutions.isEmpty) fDef.body else fDef.body.fastSubstitute(substitutions.toMap)

            newTheory = newTheory.withFunctionDefinition(
                FunctionDefinition(
                    fDef.name,
                    newAvars,
                    fDef.resultSort,
                    checkResult(newBody.typeCheckInContext(theory.signature, newAvars), fDef.resultSort), // Typecheck the body
                )
            )
        }

        problemState
        .withTheory(newTheory)
        .withFlags(
            problemState.flags.copy(
                containsItes = containsItes,
                containsExists = containsExists
            )
        )
    }
    

}