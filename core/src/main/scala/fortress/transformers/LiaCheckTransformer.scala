package fortress.transformers
import fortress.msfol._
import fortress.operations._

class LiaCheckTransformer extends ProblemStateTransformer {

    /** Takes in a Problem, applies some transformation to it, and produces a
      * new ProblemState. Note that this does not mutate the ProblemState object, only
      * produces a new one. */
    override def apply(problemState: ProblemState): ProblemState = problemState match {
        case ProblemState(theory, scopes, skolemConstants, skolemFunctions, rangeRestrictions, unapplyInterp, distinctConstants) => {

            if(scopes.contains(IntSort)) {
                var boundedSet: Set[String] = Set.empty
                var axiomVarMap: Map[Term, Set[String]] = Map.empty

                for( axiom <- problemState.theory.axioms ) {
                    val (isLia, varSet): (Boolean, Set[String]) = LiaChecker.check(axiom)

                    println(isLia + " " + varSet)
                    // only want IntSort
                    varSet.filter( v => {
                        var flag: Boolean = false
                        for( item <- problemState.theory.signature.constants ) {
                            if( item.variable.name == v && item.sort == IntSort) flag = true
                        }
                        flag
                    })
                    // get union of sets
                    if(!isLia) boundedSet = boundedSet ++ varSet
                    axiomVarMap = axiomVarMap + (axiom -> varSet)
                }

//                val n = problemState.theory.axioms.count(axiom => axiom.isLia)
                var flag: Boolean = false
                do {
                    flag = false
                    for(axiom <- problemState.theory.axioms) {
                        if( axiomVarMap(axiom).&(boundedSet).nonEmpty && axiom.isLia ) {
                            axiom.isLia = false
                            boundedSet = boundedSet ++ axiomVarMap(axiom)
                            flag = true
                        }
                    }
                } while (flag)


                val newSig = problemState.theory.signature.replaceIntSorts(boundedSet)
                val newTheory = Theory.mkTheoryWithSignature(newSig).withAxioms(problemState.theory.axioms)

                ProblemState(newTheory, scopes, skolemConstants, skolemFunctions, rangeRestrictions, unapplyInterp, distinctConstants)

            }
            else {
                problemState
            }
        }
    }

    override def name: String = "LinearArithmeticCheckTransformer"
}
