package fortress.transformers

import scala.jdk.CollectionConverters._
import fortress.msfol._
import fortress.util.Errors
import fortress.operations.TermOps._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

/** Introduces constants to simulate the domain elements, asserting these constants are
  * all distinct and replacing occurrences of domain elements with the appropriate constant.
  * Leaves other aspects of the Problem unchanged.
  */
object DomainEliminationTransformer extends ProblemStateTransformer {
    
    override def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val scopes = problemState.scopes

        val domainElemsMap: Map[Sort, Seq[DomainElement]] =
            (for(sort <- theory.sorts if !sort.isBuiltin  && scopes.contains(sort)) yield {
                val domElems = DomainElement.range(1 to scopes(sort).size, sort)
                (sort, domElems)
            }).toMap
        
        val domainConstants: Iterable[AnnotatedVar] = domainElemsMap.values.flatten.map {
            de => de.asSmtConstant of de.sort
        }

        // Assert the constants are distinct
        val distinctConstraints = for(
            (sort, domainElems) <- domainElemsMap if (domainElems.size > 1)
        ) yield Distinct(domainElems map (_.asSmtConstant))
        
        // Eliminate domain elements in existing axioms
        val convertedAxioms = theory.axioms map (_.eliminateDomainElementsConstants)

        var newSig = theory.signature
            .withConstantDeclarations(domainConstants)

        // We only remove a definition before readding it so all its dependencies are in the sig
        // definitions are basically untested
        for(cDef <- theory.signature.constantDefinitions){
            newSig = newSig.withoutConstantDefinition(cDef)
            newSig = newSig.withConstantDefinition(cDef.mapBody(_.eliminateDomainElementsConstants))
        }
        for(fDef <- theory.signature.functionDefinitions){
            newSig = newSig.withoutFunctionDefinition(fDef)
            newSig = newSig.withFunctionDefinition(fDef.mapBody(_.eliminateDomainElementsConstants))
        }

        val newTheory = Theory(newSig, convertedAxioms ++ distinctConstraints)

//            println("Theory after domain elimination:")
//            println(newTheory + "\n------------------------\n")
        
        problemState.copy(
            theory = newTheory,
            flags = problemState.flags.copy(distinctConstants = true)
        )
    }
    

}
