package fortress.operations

import java.io.StringWriter

import fortress.data.CartesianSeqProduct
import fortress.interpretation.Interpretation
import fortress.msfol._
import fortress.solverinterface.{SolverStrategy, Z3ApiSolver}
import fortress.util.Errors.AssertionException
import fortress.util._

import scala.collection.mutable.ListBuffer

class InterpretationVerifier(theory: Theory) {
    /** Given an interpretation, test all axioms of the original theory & return whether
      * they were all satisfied.
      */
    def verifyInterpretation(interpretation: Interpretation): Boolean = {
        // Utility functions to transform between Scala Booleans and Fortress ones
        def forceValueToBool(term: Value): Boolean = term match{
            case Top => true
            case Bottom => false
            case _ => throw new AssertionException("Tried to cast non-Top/Bottom Term to Boolean")
        }
        def boolToValue(b: Boolean): Value = if(b) Top else Bottom

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

        // Given a function and its arguments, look inside the interpretation to find the result
        def appInterpretations(fnName: String, evaluatedArgs: Seq[Value]): Value = {
            // Retrieve FuncDecl signature from the theory (used to index the interpretation)
            val fnSignature = theory.signature.functionDeclarations.filter(fd => fd.name == fnName).head
            val fnInterpretation = interpretation.functionInterpretations(fnSignature)
            // Below type conversion is a lil sketch (narrowing conversion?)
            fnInterpretation(evaluatedArgs.asInstanceOf[Seq[Value]])
        }

        // Given a builtin function and its arguments, run it through a throwaway Z3 solver for the result
        // (to avoid having to implement every function manually on our end)
        def evaluateBuiltIn(fn: BuiltinFunction, evalArgs: Seq[Value]): Value = {
            val solver: SolverStrategy = new Z3ApiSolver
            val evalResult: Var = Var("!VERIFY_INTERPRETATION_RES")
            val evalResultAnnotated: AnnotatedVar = fn match{
                case IntPlus | IntNeg | IntSub | IntMult | IntDiv | IntMod => evalResult of Sort.Int
                case BvPlus | BvNeg | BvSub | BvMult | BvSignedDiv | BvSignedRem | BvSignedMod =>
                    evalResult of Sort.BitVector(evalArgs.head.asInstanceOf[BitVectorLiteral].bitwidth);
                case IntLE | IntLT | IntGE | IntGT |
                     BvSignedLE | BvSignedLT | BvSignedGE | BvSignedGT => evalResult of Sort.Bool
                case _ => throw new scala.NotImplementedError("Builtin function not accounted for")
            }
            val theory: Theory = Theory.empty
                .withConstant(evalResultAnnotated)
                .withAxiom(evalResult === BuiltinApp(fn, evalArgs))
            solver.solve(theory, Milliseconds(1000), Seq.empty)
            val solvedInstance = solver.getInstance(theory)
            solvedInstance.constantInterpretations(evalResultAnnotated)
        }

        // Recursively evaluates a given expression to either Top or Bottom, starting from the root
        def evaluate(term: Term): Value = term match{
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
            case App(fname, args) => appInterpretations(fname, args.map(arg => evaluate(arg)))
            case BuiltinApp(fn, args) => evaluateBuiltIn(fn, args.map(arg => evaluate(arg)))
            case Forall(vars, body) => {
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
