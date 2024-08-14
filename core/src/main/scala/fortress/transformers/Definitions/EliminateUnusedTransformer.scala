package fortress.transformers.Definitions

import fortress.interpretation.{BasicInterpretation, Interpretation}
import fortress.msfol._
import fortress.operations.NaturalSetAccumulation
import fortress.problemstate.ProblemState
import fortress.transformers.ProblemStateTransformer

/**
  * Eliminate symbols that are not used.
  * Note: does not currently eliminate sorts.
  */
object EliminateUnusedTransformer extends ProblemStateTransformer {

    // An overapproximation: will also accumulate bound variable names, so we won't eliminate names that
    // aren't used but are shadowed by bound variables.
    private object AccumulateUsedNames extends NaturalSetAccumulation[String] {
        override val exceptionalMappings: PartialFunction[Term, Set[String]] = {
            case Var(name) => Set(name)
            case App(name, args) => Set(name) ++ args.map(naturalRecur).fold(Set.empty)(_ union _)
        }
    }

    override def apply(problemState: ProblemState): ProblemState = {
        // Compute an overapproximation of all the names that are ever used
        var usedNames = (problemState.theory.axioms map AccumulateUsedNames.naturalRecur).fold(Set.empty)(_ union _)
        var newNames = usedNames
        while (newNames.nonEmpty) {
            val currentNames = newNames flatMap { name =>
                problemState.theory.functionDefinitions
                    .find(_.name == name)
                    .map(fDef => AccumulateUsedNames.naturalRecur(fDef.body))
                    .getOrElse {
                        problemState.theory.constantDefinitions
                            .find(_.name == name)
                            .map(cDef => AccumulateUsedNames.naturalRecur(cDef.body))
                            .getOrElse(Set())
                    }
            }
            newNames = currentNames -- newNames
            usedNames = usedNames ++ currentNames
        }

        val fDecls = problemState.theory.functionDeclarations.filter(usedNames contains _.name)
        val cDecls = problemState.theory.constantDeclarations.filter(usedNames contains _.name)
        val fDefs = problemState.theory.functionDefinitions.filter(usedNames contains _.name)
        val cDefs = problemState.theory.constantDefinitions.filter(usedNames contains _.name)

        val unapply: Interpretation => Interpretation = interp => {
            // Use trivial interpretations for the function/constant declarations we filtered out
            val trivialInterp = problemState.theory.signature.trivialInterpretation(problemState.scopes)
            val newFuncInterps = (
                for (fDecl <- problemState.theory.functionDeclarations)
                    yield fDecl -> interp.functionInterpretations.getOrElse(fDecl, trivialInterp.functionInterpretations(fDecl))
            ).toMap
            val newConstInterps = (
                for (cDecl <- problemState.theory.constantDeclarations)
                    yield cDecl -> interp.constantInterpretations.getOrElse(cDecl, trivialInterp.constantInterpretations(cDecl))
            ).toMap
            BasicInterpretation(
                interp.sortInterpretations,
                newConstInterps,
                newFuncInterps,
                interp.functionDefinitions,
            )
        }

        problemState.copy(theory = problemState.theory.copy(
            signature = problemState.theory.signature.copy(
                functionDeclarations = fDecls,
                constantDeclarations = cDecls,
                functionDefinitions = fDefs,
                constantDefinitions = cDefs,
            ),
        )).withUnapplyInterp(unapply)
    }

}
