package fortress.transformers

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.operations._
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState

object  ScopeNonExactPredicatesTransformer extends ProblemStateTransformer {

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
            /*
            NAD: removed these axioms to allow the predicate to not be satisfied by
                 any elements and therefore allow the sort to be empty for a non-exact scope
                 2023-06-26
                 These were added likely for comparison with nondistinct constants method,
                 which requires there to be at least one value.
                 
            val antiVacuityAxioms = for {
                sort <- theory.sorts
                if scopes.contains(sort) && !scopes(sort).isExact
            } yield {
                Exists(Var("x") of sort, App(ScopeNonExactPredicates.nonExactScopePred(sort), Var("x")))
            }
            */
            // Constants and functions must have ranges in the subtypes
            val constantAxioms = for (av <- theory.constantDeclarations if scopes.contains(av.sort) && !scopes(av.sort).isExact ) yield App(ScopeNonExactPredicates.nonExactScopePred(av.sort), av.variable)

            val functionAxioms = for {
                fdecl <- theory.functionDeclarations
                if scopes.contains(fdecl.resultSort) && !scopes(fdecl.resultSort).isExact
            } yield {
                val argsAnnotated = fdecl.argSorts.zipWithIndex.map { case (sort, index) => Var(s"x_${sort}_${index}") of sort }

                // For each arg with a non-exact scope, add a hypothesis that the arg is in its sort
                val guards = argsAnnotated
                    .filter { arg => !scopes(arg.sort).isExact }
                    .map { arg => App(ScopeNonExactPredicates.nonExactScopePred(arg.sort), arg.variable) }

                // Suppose f: AxB->C and all are non-exact. Generate the following axiom:
                // forall a: A, b: B . inA(a) && inB(b) => inC(f(a,b))
                val outputPred = ScopeNonExactPredicates.nonExactScopePred(fdecl.resultSort)
                Forall(argsAnnotated,
                    Implication(And.smart(guards),
                        App(outputPred, App(fdecl.name, argsAnnotated.map(_.variable)))))
            }

            val resultTheory = theory
              .withFunctionDeclarations(scopeNonExactPreds)
              .someAxioms(ScopeNonExactPredicates.addBoundsPredicates, scopes)
              // NAD see note above
              //.withAxioms(antiVacuityAxioms)
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
