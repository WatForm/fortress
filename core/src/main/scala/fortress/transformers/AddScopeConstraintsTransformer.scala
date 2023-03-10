package fortress.transformers
import fortress.interpretation.Interpretation
import fortress.problemstate._
import fortress.msfol._
import fortress.operations._

/*
    This transformer should be used with RSVIncrementalModelFinder,
    introduce a bool variable for each unbounded sort.
 */
object AddScopeConstraintsTransformer extends ProblemStateTransformer {
    /** Takes in a Problem, applies some transformation to it, and produces a
      * new ProblemState. Note that this does not mutate the ProblemState object, only
      * produces a new one. */

    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {

            val constants: Set[AnnotatedVar] =
                for(sort <- theory.sorts) yield AnnotatedVar(Var(sort.name + "_GT"), BoolSort)


            // for each sort S, yield constraint ~(S_GT)
            val newAxioms: Set[Term] = {
                var tmp: Set[Term] = Set.empty
                for (sort <- theory.sorts) {
                    val term: Term = Not(Var(sort.name + "_GT"))
                    term.named = sort.name + "_G"
                    tmp = tmp + term
                }
                tmp
            }

            val resultTheory = theory
                .withConstants(constants)
                .withAxioms(newAxioms)

            val unapply: Interpretation => Interpretation = {
                interp => {
                    interp.withoutConstants(constants)
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

    override def name: String = "Add constraints about scope sizes"
}
