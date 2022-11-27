package fortress.transformers

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.operations._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

class ScopeNonExactPredicatesTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {

            val scopeNonExactPreds = for {
                sort <- theory.sorts
                if scopes.contains(sort) && !scopes(sort).isExact
            } yield {
                val predName = ScopeNonExactPredicates.nonExactScopePred(sort)  // " __@Pred_{sort.name} "
                val predDecl = FuncDecl(predName, sort, BoolSort)
                predDecl
            }

            // Have to say the subtypes are nonempty
            val antiVacuityAxioms = for {
                sort <- theory.sorts
                if scopes.contains(sort) && !scopes(sort).isExact
            } yield {
                Exists(Var("x") of sort, App(ScopeNonExactPredicates.nonExactScopePred(sort), Var("x")))
            }

            // Constants and functions must have ranges in the subtypes
            val constantAxioms = for (av <- theory.constants) yield App(ScopeNonExactPredicates.nonExactScopePred(av.sort), av.variable)

            val functionAxioms = for {
                fdecl <- theory.functionDeclarations
                if scopes.contains(fdecl.resultSort) && !scopes(fdecl.resultSort).isExact
            } yield {
                val argsAnnotated = fdecl.argSorts.zipWithIndex.map { case (sort, index) => Var(s"x_${sort}_${index}") of sort }
                val outputPred = ScopeNonExactPredicates.nonExactScopePred(fdecl.resultSort)
                // We don't need to check that the inputs are in the subtypes, such inputs don't have any affect on the formulas
                Forall(argsAnnotated, App(outputPred, App(fdecl.name, argsAnnotated.map(_.variable))))
            }

            val resultTheory = theory
              .withFunctionDeclarations(scopeNonExactPreds)
              .someAxioms(ScopeNonExactPredicates.addBoundsPredicates, scopes)
              .withAxioms(antiVacuityAxioms)
              .withAxioms(constantAxioms)
              .withAxioms(functionAxioms)

            val unapply: Interpretation => Interpretation = {
                interp => {
                    var resultInterp = interp
                    val sortInterp: Map[Sort, Seq[Value]] = interp.sortInterpretations
                    for(pred <- scopeNonExactPreds) {
                        val sort: Sort = pred.argSorts.head
                        val Interp: Seq[Value] = sortInterp(sort).filter(value => {
                            interp.getFunctionValue(pred.name, Seq(value)) == Top
                        })
                        resultInterp = resultInterp.updateSortInterpretations(sort, Interp)
                    }
                    resultInterp.withoutFunctions(scopeNonExactPreds)
                }
            }

            ProblemState(
                resultTheory,
                scopes, skc,
                skf,
                rangeRestricts,
                unapply :: unapplyInterp,
                distinctConstants
            )
        }
    }

    override def name: String = "NonExactScopePredicatesTransformer"

}
