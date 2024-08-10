package fortress.transformers

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate._

/** Introduces enum values to simulate the domain elements, replacing occurrences
  * of domain elements with the appropriate constant. Leaves other aspects of the
  * Problem unchanged.
  * 
  * Any Enums present in the Theory will be converted to datatype declarations in SMT-LIB.
  * Thus this effectively makes the method use datatype declarations in SMT-LIB to represent
  * the constants.
  * This should not be used with the DEsToConstantsTransformers
  */
object DEsToEnumsTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes
        
        val enumValuesMap: Map[Sort, Seq[EnumValue]] =
            (for (sort <- theory.sorts if !sort.isBuiltin && scopes.contains(sort)) yield {
                val enumValues = DomainElement.range(1 to scopes(sort).size, sort).map(_.asEnumValue)
                (sort, enumValues)
            }).toMap

        // Convert domain elements in existing axioms to enum values
        val convertedAxioms = theory.axioms map (_.eliminateDomainElementsEnums)
        
        var newSig = theory.signature
        // We only remove a definition before readding it so all its dependencies are in the sig
        // definitions are basically untested
        for(cDef <- theory.signature.constantDefinitions){
            newSig = newSig.withoutConstantDefinition(cDef)
            newSig = newSig.withConstantDefinition(cDef.mapBody(_.eliminateDomainElementsEnums))
        }
        for(fDef <- theory.signature.functionDefinitions){
            newSig = newSig.withoutFunctionDefinition(fDef)
            newSig = newSig.withFunctionDefinition(fDef.mapBody(_.eliminateDomainElementsEnums))
        }


        var newTheory = Theory(newSig, convertedAxioms)

        newTheory = enumValuesMap.foldLeft(newTheory) {
            case (t, (s, enumValueSeq)) => t.withEnumSort(s, enumValueSeq: _*)
        }


        //ProblemState(newTheory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants = false)
        problemState.copy(
            theory = newTheory,
            flags = problemState.flags.copy(distinctConstants = false)
        )
    }


}
