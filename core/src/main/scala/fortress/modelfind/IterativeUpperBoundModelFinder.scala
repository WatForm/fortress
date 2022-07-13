package fortress.modelfind

import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.util.Maps.NondeterministicMap
import fortress.util.Seconds

import scala.collection.parallel.CollectionConverters._
import scala.collection.parallel.immutable.ParVector

class IterativeUpperBoundModelFinder
  extends ModelFinder
    with ModelFinderSettings {

    var interpretation: Option[Interpretation] = None

    override def checkSat(): ModelFinderResult = {
        val scopeRanges: Map[Sort, Range] = for ((sort, scope) <- analysisScopes) yield (sort -> (1 to scope))
        val nScopeMap: NondeterministicMap[Sort, Int] = NondeterministicMap.fromLists(scopeRanges)


        def computeResult(scopes: Map[Sort, Int]): ModelFinderResult = {
            val modelFinder = new FortressFOUR_SI
            modelFinder.setTheory(theory)
            for ((sort, scope) <- scopes) {
                modelFinder.setAnalysisScope(sort, scope)
            }
            modelFinder.setTimeout(Seconds(100000))
            // modelFinder.setBoundedIntegers(integerSemantics)

            val result = modelFinder.checkSat()
            if (result.equals(SatResult)) {
                interpretation = Some(modelFinder.viewModel())
            }

            result
        }
        // TODO have to order these
        for (scopes <- nScopeMap.singleStepMap.possibleValues) {
            val result = computeResult(scopes)
            result match {
                case SatResult | ErrorResult(_) | TimeoutResult | UnknownResult => return result
                case UnsatResult => {}
            }
        }
        UnsatResult
    }

    override def viewModel(): Interpretation = {
        interpretation.get
    }

    override def nextInterpretation(): ModelFinderResult = ???

    override def countValidModels(newTheory: Theory): Int = ???

    override def close(): Unit = ???

}

class ParallelIterativeUpperBoundModelFinder
  extends ModelFinder
    with ModelFinderSettings {

    var interpretation: Option[Interpretation] = None

    override def checkSat(): ModelFinderResult = {
        val scopeRanges: Map[Sort, Range] = for ((sort, scope) <- analysisScopes) yield (sort -> (1 to scope))
        val nScopeMap: NondeterministicMap[Sort, Int] = NondeterministicMap.fromLists(scopeRanges)
        // TODO have to order these
        val possibleScopes: ParVector[Map[Sort, Int]] = nScopeMap.singleStepMap.possibleValues.toVector.par

        def computeResult(scopes: Map[Sort, Int]): ModelFinderResult = {
            val modelFinder = new FortressFOUR_SI
            modelFinder.setTheory(theory)
            for ((sort, scope) <- scopes) {
                modelFinder.setAnalysisScope(sort, scope)
            }
            modelFinder.setTimeout(Seconds(100000))
            // modelFinder.setBoundedIntegers(integerSemantics)

            val result = modelFinder.checkSat()
            if (result.equals(SatResult)) {
                interpretation = Some(modelFinder.viewModel())
            }

            result
        }

        if (possibleScopes.exists(scopes => computeResult(scopes) == SatResult)) SatResult
        else UnsatResult
    }

    override def viewModel(): Interpretation = {
        interpretation.get
    }

    override def nextInterpretation(): ModelFinderResult = ???

    override def countValidModels(newTheory: Theory): Int = ???

    override def close(): Unit = ???
}