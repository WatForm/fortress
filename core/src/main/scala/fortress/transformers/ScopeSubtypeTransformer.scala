package fortress.transformers

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.operations._
import fortress.operations.TheoryOps._

class ScopeSubtypeTransformer extends ProblemStateTransformer {

    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {

            val scopeSubtypePreds = for {
                sort <- theory.sorts
                if scopes.contains(sort) && !scopes(sort).isExact
            } yield {
                val predName = ScopeSubtype.subtypePred(sort)  // " __@Pred_{sort.name} "
                val predDecl = FuncDecl(predName, sort, BoolSort)
                predDecl
            }

            // Have to say the subtypes are nonempty
            val antiVacuityAxioms = for {
                sort <- theory.sorts
                if scopes.contains(sort) && !scopes(sort).isExact
            } yield {
                Exists(Var("x") of sort, App(ScopeSubtype.subtypePred(sort), Var("x")))
            }

            // Constants and functions must have ranges in the subtypes
            val constantAxioms = for (av <- theory.constants) yield App(ScopeSubtype.subtypePred(av.sort), av.variable)

            val functionAxioms = for {
                fdecl <- theory.functionDeclarations
                if scopes.contains(fdecl.resultSort) && !scopes(fdecl.resultSort).isExact
            } yield {
                val argsAnnotated = fdecl.argSorts.zipWithIndex.map { case (sort, index) => Var(s"x_${sort}_${index}") of sort }
                val outputPred = ScopeSubtype.subtypePred(fdecl.resultSort)
                // We don't need to check that the inputs are in the subtypes, such inputs don't have any affect on the formulas
                Forall(argsAnnotated, App(outputPred, App(fdecl.name, argsAnnotated.map(_.variable))))
            }

            val resultTheory = theory
              .withFunctionDeclarations(scopeSubtypePreds)
              .someAxioms(ScopeSubtype.addBoundsPredicates, scopes)
              .withAxioms(antiVacuityAxioms)
              .withAxioms(constantAxioms)
              .withAxioms(functionAxioms)

            val unapply: Interpretation => Interpretation = {
                interp => {
                    var resultInterp = interp
                    for (pred <- scopeSubtypePreds) {  // for each subtype predicate funcDecl
                        val sort: Sort = pred.argSorts.head // get argument sort
                        // filter: get preds whose result sort is Top(True)
                        val domainElements: Seq[Value] = interp.functionInterpretations(pred).toSeq.filter(pred => pred._2 == Top).map(_._1.head)
                        resultInterp = resultInterp.updateSortInterpretations(sort, domainElements)
                    }
                    resultInterp
                }
            }

            println("Theory after scope subtype transformer:\n")
            println(resultTheory + "\n-----------------------------\n")

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

    override def name: String = "Scope Subtype Transformer"

}
