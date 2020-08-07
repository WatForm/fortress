package fortress.compiler

import fortress.msfol._
import fortress.transformers._
import fortress.util._
import fortress.interpretation._

trait TransformationCompiler extends LogicCompiler {
    override def compile(
        theory: Theory,
        scopes: Map[Sort, Int],
        timeout: Milliseconds
    ): Either[CompilerError, CompilerResult] = {
        val initialProblemState = ProblemState(theory, scopes)
        val finalProblemState = transformerSequence.foldLeft(initialProblemState)((pState, transformer) => transformer(pState))
        
        object Result extends CompilerResult {
            override val theory: Theory = finalProblemState.theory

            override def decompileInterpretation(interpretation: Interpretation): Interpretation = {
                finalProblemState.unapplyInterp.foldLeft(interpretation) {
                    (interp, unapplyFn) => unapplyFn(interp)
                }
            }

            override def skipForNextInterpretation: Set[Declaration] = {
                // We have to use some type hackery to get around the invariance of Set[A]
                (finalProblemState.skolemConstants.map(x => x: Declaration)) union finalProblemState.skolemFunctions.map(x => x: Declaration)
            }
        }
        
        Right(Result)
    }

    def transformerSequence: Seq[ProblemStateTransformer]
}
