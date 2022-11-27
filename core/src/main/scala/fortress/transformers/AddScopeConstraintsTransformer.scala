package fortress.transformers
import fortress.interpretation.Interpretation
import fortress.problemstate._
import fortress.msfol._
import fortress.operations._

object AddScopeConstraintsTransformer extends ProblemStateTransformer {
    /** Takes in a Problem, applies some transformation to it, and produces a
      * new ProblemState. Note that this does not mutate the ProblemState object, only
      * produces a new one. */

    override def apply(problemState: ProblemState): ProblemState = {

        case ProblemState(theory, scopes, skc, skf, rangeRestricts, unapplyInterp, distinctConstants) => {

            val constants: Set[AnnotatedVar] = {
                var temp: Set[AnnotatedVar] = Set.empty
                for(sort <- theory.sorts) {
                    temp = temp + AnnotatedVar(Var(sort.name + "_LT"), BoolSort) + AnnotatedVar(Var(sort.name + "_GT"), BoolSort)
                }
                temp
            }

            val clauses: Map[Sort, Seq[Term]] = {
                var temp : Map[Sort, Seq[Term]] = Map.empty
                for( sort <- problemState.theory.sorts ) {
                    val c1: Term = Var(sort.name + "_LT")
                    val c2: Term = Var(sort.name + "_GT")
                    temp = temp + (sort, Seq(c1, c2))
                }
                temp
            }

            var newAxioms: Set[Term] = for( axiom <- problemState.theory.axioms ) yield AddScopeConstraints.addScopeConstraints(axiom, clauses)

            for( sort <- problemState.theory.sorts ) {
                newAxioms = newAxioms + Not(clauses(sort).head) + Not(clauses(sort).last)
            }

            val resultTheory = theory
                    .withConstants(constants) // add scope constants, two new constants for each sort
                    .withoutAxioms(theory.axioms) // remove old axioms
                    .withAxioms(newAxioms) // add new axioms with scope constraints

            val unapply: Interpretation => Interpretation = ???

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
