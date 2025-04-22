// should eventually integrate into the standard compiler

package fortress.compilers

//import fortress.msfol._
import fortress.transformers._
import fortress.transformers.TheoryTransformer._ // for implicit conversion to ProblemStateTransformer
//import fortress.modelfind._
import fortress.symmetry._
import scala.collection.mutable.ListBuffer


class SymmetryDisjLimitThreeCompiler extends StandardCompiler {

    override def symmetryBreaker:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(new SymmetryBreakingTransformer(SymmetryBreakingOptions(
            selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
            breakSkolem = true,
            sortInference = false,
            patternOptimization = true,
            disjLimit = Option(3)
        )))
}

class SymmetryDisjLimitFiveCompiler extends StandardCompiler {

    override def symmetryBreaker:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(new SymmetryBreakingTransformer(SymmetryBreakingOptions(
            selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
            breakSkolem = true,
            sortInference = false,
            patternOptimization = true,
            disjLimit = Option(5)
        )))
}

class SymmetryDisjLimitEightCompiler extends StandardCompiler {

    override def symmetryBreaker:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(new SymmetryBreakingTransformer(SymmetryBreakingOptions(
            selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
            breakSkolem = true,
            sortInference = false,
            patternOptimization = true,
            disjLimit = Option(8)
        )))
}

class SymmetryDisjLimitTenCompiler extends StandardCompiler {

    override def symmetryBreaker:ListBuffer[ProblemStateTransformer] =
        CompilersRegistry.ListOfOne(new SymmetryBreakingTransformer(SymmetryBreakingOptions(
            selectionHeuristic = MonoFirstThenFunctionsFirstAnyOrder,
            breakSkolem = true,
            sortInference = false,
            patternOptimization = true,
            disjLimit = Option(10)
        )))
}
