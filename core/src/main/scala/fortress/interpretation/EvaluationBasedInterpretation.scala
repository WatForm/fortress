package fortress.interpretation

import fortress.msfol._
import fortress.solverinterface._
import fortress.data.CartesianSeqProduct
import fortress.util.ArgumentListGenerator

// Use vals and not defs - want to move information out of the solver immediately
// in case we want to close the connection to it
abstract class EvaluationBasedInterpretation(sig: Signature) extends Interpretation {
    protected def evaluateConstant(c: AnnotatedVar): Value
    protected def evaluateSort(s: Sort): Seq[Value]
    protected def evaluateFunction(f: FuncDecl, argList: Seq[Value]): Value
    
    private def scopes: Map[Sort, Int] = for((sort, seq) <- sortInterpretations) yield (sort -> seq.size)
    
    override val constantInterpretations: Map[AnnotatedVar, Value] = {
        for {
            c <- sig.constants
            if DomainElement.interpretName(c.name).isEmpty // Exclude domain constants
		} yield (c -> evaluateConstant(c))
    }.toMap
    
    override val sortInterpretations: Map[Sort, Seq[Value]] = {
        for(sort <- sig.sorts) yield (sort -> evaluateSort(sort))
    }.toMap
    
    override val functionInterpretations: Map[fortress.msfol.FuncDecl, Map[Seq[Value], Value]] = {
        for(f <- sig.functionDeclarations) yield (f -> {
            for(argList <- ArgumentListGenerator.generate(f, scopes))
            yield (argList -> evaluateFunction(f, argList))
        }.toMap)
    }.toMap
}
