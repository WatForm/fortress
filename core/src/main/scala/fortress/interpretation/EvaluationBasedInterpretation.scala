package fortress.interpretation

import fortress.msfol._
import fortress.solvers._
import fortress.data.CartesianSeqProduct
import fortress.util.ArgumentListGenerator

/** An interpretation which gets its interpretations of signature elements through some kind of evaluation function,
  * for example from a connection to an SMT solver's interpretation.
  */
abstract class EvaluationBasedInterpretation(sig: Signature) extends Interpretation {
    protected def evaluateConstant(c: AnnotatedVar): Value
    protected def evaluateSort(s: Sort): Seq[Value]
    protected def evaluateFunction(f: FuncDecl, scopes: Map[Sort, Int]): Map[Seq[Value], Value]
    protected def evaluateFunctionDefinition(): Set[FunctionDefinition]
    
    protected def scopes: Map[Sort, Int] = for((sort, seq) <- sortInterpretations) yield (sort -> seq.size)
    
    // Use vals and not defs - want to move information out of the solver immediately
    // in case we want to close the connection to it

    override val constantInterpretations: Map[AnnotatedVar, Value] = {
        for {
            c <- sig.constantDeclarations
            if DomainElement.interpretName(c.name).isEmpty // Exclude domain constants
		} yield (c -> evaluateConstant(c))
    }.toMap

    override val sortInterpretations: Map[Sort, Seq[Value]] = {
        for (sort <- sig.sorts) yield sort -> evaluateSort(sort)
    }.toMap ++ (sig.enumConstants transform ((_, v) => v.map(x => DomainElement.interpretName(x.name).get)))
    
    override val functionInterpretations: Map[fortress.msfol.FuncDecl, Map[Seq[Value], Value]] = {
            for(f <- sig.functionDeclarations) yield (f -> evaluateFunction(f, scopes))
    }.toMap

    override val functionDefinitions: Set[FunctionDefinition] = evaluateFunctionDefinition()
}
