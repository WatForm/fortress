package fortress.transformers.Integers

import fortress.transformers.ProblemStateTransformer
import fortress.problemstate.ProblemState
import fortress.data.IntSuffixNameGenerator
import fortress.msfol.Sort
import fortress.operations.IntegerToSortConverter
import fortress.msfol._
import fortress.problemstate.ExactScope

object PermissiveFiniteIntsTransformer extends ProblemStateTransformer {
    def apply(ps: ProblemState): ProblemState = {
        val intScope = ps.scopes.getOrElse(IntSort, ExactScope(0)).size
        if (intScope == 0){
            return ps
        }

        
        val originalTheory = ps.theory
        val nameGen = IntSuffixNameGenerator.restrictAllNamesInTheory(originalTheory)
        val finiteIntSort = SortConst(nameGen.freshName("FiniteInt"))

        
        // Assuming [-scope/2, scope/2)
        val min = -intScope / 2
        val max = intScope / 2 - 1

        val int2sort = new IntegerToSortConverter(
            min, max, finiteIntSort, nameGen
        )

        val psWithIntSort = int2sort.transformProblemState(ps)

        val permissive = new PermissiveTransformer(int2sort.overflows())

        val result = permissive.apply(psWithIntSort)

        return result
    }
}