package fortress.operations

import java.io.StringWriter

import fortress.data.CartesianSeqProduct
import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.solverinterface.Z3IncSolver
import fortress.util.Errors
import fortress.util._
import fortress.msfol.DSL._

import scala.collection.mutable.ListBuffer

class InterpretationVerifier(theory: Theory) {
    // Utility functions to transform between Scala Booleans and Fortress ones
    private def forceValueToBool(term: Value): Boolean = term match{
        case Top => true
        case Bottom => false
        case _ => Errors.Internal.impossibleState("Tried to cast non-Top/Bottom Term to Boolean")
    }
    
    private  def boolToValue(b: Boolean): Value = if(b) Top else Bottom
    /** Given an interpretation, test all axioms of the original theory & return whether
      * they were all satisfied.
      */
    def verifyInterpretation(interpretation: Interpretation): Boolean = {
        // Context: A mapping of Vars to ListBuffer[Term]s (used as a stack).
        // The head of the ListBuffer will always hold the innermost binding of the Var,
        // with the "default" context being the base interpretation itself.
        val context: scala.collection.mutable.Map[Var, ListBuffer[Value]] =
        scala.collection.mutable.Map() ++ interpretation.constantInterpretations.map{
            // Conversion from AnnotatedVar to Var is safe since names are distinct
            case (key, value) => (key.variable, ListBuffer[Value](value))
        }
        def pushToContext(key: Var, value: Value): Unit = {
            if(context.contains(key)) value +=: context(key)
            else context(key) = ListBuffer[Value](value)
        }
        def popFromContext(key: Var): Unit = {
            if(context(key).length == 1) context -= key
            else context(key).remove(0)
        }

        // Recursively evaluates a given expression to either Top or Bottom, starting from the root
        def evaluate(term: Term): Value = term match {
            // "Atomic" terms should be maintained as-is
            case Top | Bottom | EnumValue(_) | DomainElement(_, _) |
                 IntegerLiteral(_) | BitVectorLiteral(_, _) => term.asInstanceOf[Value]
            case v @ Var(_) => context(v).head
            case Not(p) => boolToValue(!forceValueToBool(evaluate(p)))
            case AndList(args) => boolToValue(args.forall(a => forceValueToBool(evaluate(a))))
            case OrList(args) => boolToValue(args.exists(a => forceValueToBool(evaluate(a))))
            case Distinct(args) => boolToValue(
                args.size ==
                    args.map(a => evaluate(a)).distinct.size
            )
            case Implication(p, q) => boolToValue(
                !forceValueToBool(evaluate(p)) || forceValueToBool(evaluate(q))
            )
            case Iff(p, q) => boolToValue(
                forceValueToBool(evaluate(p)) == forceValueToBool(evaluate(q))
            )
            // The operands to Eq are expected to be case classes, so equality works as expected
            case Eq(l, r) => boolToValue(evaluate(l) == evaluate(r))
            case IfThenElse(condition, ifTrue, ifFalse) => {
                if(forceValueToBool(evaluate(condition))) evaluate(ifTrue)
                else evaluate(ifFalse)
            }
            case App(fname, args) => interpretation.getFunctionValue(fname, args.map(arg => evaluate(arg)))
            case BuiltinApp(fn, args) => interpretation.evaluateBuiltIn(fn, args.map(arg => evaluate(arg)))
            case Forall(vars, body) => {
                val varDomains = vars.map(v =>
                    interpretation.sortInterpretations(v.sort).toIndexedSeq
                ).toIndexedSeq
                val allPossibleValueLists = new CartesianSeqProduct[Value](varDomains)
                // Going through all possible combinations of the domain elements:
                // append to the context, recurse, then remove from the context
                for(valueList <- allPossibleValueLists) {
                    valueList.zipWithIndex.foreach {
                        case (value, index) => pushToContext(vars(index).variable, value)
                    }
                    val res = forceValueToBool(evaluate(body))
                    valueList.zipWithIndex.foreach {
                        case (value, index) => popFromContext(vars(index).variable)
                    }
                    if(!res){
                        return Bottom
                    }
                }
                Top
            }
            case Exists(vars, body) => {

                val varDomains = vars.map(v =>
                    interpretation.sortInterpretations(v.sort).toIndexedSeq
                ).toIndexedSeq
                val allPossibleValueLists = new CartesianSeqProduct[Value](varDomains)
                // Going through all possible combinations of the domain elements:
                // append to the context, recurse, then remove from the context
                for(valueList <- allPossibleValueLists){
                    valueList.zipWithIndex.foreach {
                        case (value, index) => pushToContext(vars(index).variable, value)
                    }
                    val res = forceValueToBool(evaluate(body))
                    valueList.zipWithIndex.foreach {
                        case (value, index) => popFromContext(vars(index).variable)
                    }
                    if(res){
                        return Top
                    }
                }
                Bottom
            }
        }
        for(axiom <- theory.axioms){
            val result = forceValueToBool(evaluate(axiom))
            // println(axiom.toString + " evaluated to " + result)
            if(!result){
                return false
            }
        }
        // println("All axioms satisfied")
        true
    }
}
