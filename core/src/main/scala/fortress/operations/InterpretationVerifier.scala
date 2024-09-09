package fortress.operations

import java.io.StringWriter

import fortress.data.CartesianSeqProduct
import fortress.interpretation.Interpretation
import fortress.msfol._
// import fortress.solvers.Z3NonIncSolver
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

    private def wrapBv(value: Int, bitwidth: Int): BitVectorLiteral =
        BitVectorLiteral(value & ((1 << bitwidth) - 1), bitwidth)
    
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
            case BuiltinApp(fn, unprocessedArgs) => {
                // Note that currently we arbitrarily force division by 0 to be equal to 0
                val args = unprocessedArgs.map(evaluate)
                fn match {
                    case f: BinaryIntegerFunction => {
                        // Get integer values from args
                        val intArgs = args map (_ match {
                            case IntegerLiteral(value) => value
                            case _ => Errors.Internal.impossibleState("Non-integer arguments to integer function or relation")
                        })
                        val x = intArgs(0)
                        val y = intArgs(1)

                        IntegerLiteral(f match {
                            case IntSub => x - y
                            case IntPlus => x + y
                            case IntMult => x * y
                            case IntDiv => y match {
                                case 0 => 0 // Arbitrary value for divide by zero
                                case _ => x / y
                            }
                            case IntMod => y match {
                                case 0 => 0 // Arbitrary value for mod by zero
                                case _ => x % y
                            }
                        })
                    }
                    case f: BinaryIntegerRelation => {
                        val (x, y) = args match {
                            case Seq(IntegerLiteral(x), IntegerLiteral(y)) => (x, y)
                            case _ => Errors.Internal.impossibleState("Wrong size or type of arguments to integer function or relation")
                        }
                        boolToValue(f match {
                            case IntGE => x >= y
                            case IntGT => x > y
                            case IntLE => x <= y
                            case IntLT => x < y
                        })
                    }
                    case f: BinaryBitVectorFunction => {
                        val (x, y, bitwidth) = args match {
                            case Seq(BitVectorLiteral(x, bw1), BitVectorLiteral(y, bw2)) if bw1 == bw2 => (x, y, bw1)
                            case _ => Errors.Internal.impossibleState("Invalid args for binary bitvector function")
                        }

                        f match {
                            case BvMult => wrapBv(x * y, bitwidth)
                            case BvPlus => wrapBv(x + y, bitwidth)
                            case BvSub => wrapBv(x - y, bitwidth)
                            case BvSignedDiv => y match {
                                case 0 => BitVectorLiteral(0, bitwidth) // arbitrary divide by zero value
                                case _ => wrapBv(x / y, bitwidth)
                            }
                            case BvSignedMod => y match {
                                case 0 => BitVectorLiteral(0, bitwidth) // arbitrary divide by zero value
                                case _ => wrapBv((x.abs % y.abs) * y.sign, bitwidth)
                            }
                            case BvSignedRem => y match {
                                case 0 => BitVectorLiteral(0, bitwidth) // arbitrary divide by zero value
                                case _ => wrapBv((x.abs % y.abs) * x.sign, bitwidth)
                            }
                        }
                    }
                    case f: BinaryBitVectorRelation => {
                        val (x, y, bitwidth) = args match {
                            case Seq(BitVectorLiteral(x, bw1), BitVectorLiteral(y, bw2)) if bw1 == bw2 => (x, y, bw1)
                            case _ => Errors.Internal.impossibleState("Invalid args for binary bitvector function")
                        }

                        boolToValue (f match {
                            case BvSignedGE => x >= y
                            case BvSignedGT => x > y
                            case BvSignedLE => x <= y
                            case BvSignedLT => x < y
                        })
                    }
                    case IntNeg => {
                        args match {
                            case Seq(IntegerLiteral(x)) => IntegerLiteral(-x)
                            case _ => Errors.Internal.impossibleState("Invalid arguments to integer negation")
                        }
                    }
                    case CastIntToBV(bitwidth) => {
                        args match {
                            case Seq(IntegerLiteral(x)) => wrapBv(x, bitwidth)
                            case _ => Errors.Internal.impossibleState("Invalid arguments to integer cast to bitvector")
                        }
                    }
                    case CastBVToInt => {
                        args match {
                            case Seq(BitVectorLiteral(x, _)) => IntegerLiteral(x)
                            case _ => Errors.Internal.impossibleState("Attempting to cast non-bitvector to int")
                        }
                    }
                    case BvConcat => {
                        args match {
                            case Seq(BitVectorLiteral(x, bw1), BitVectorLiteral(y, bw2)) =>
                                wrapBv((x << bw2) | y, bw1 + bw2)
                        }
                    }
                    case BvNeg => {
                        args match {
                            case Seq(BitVectorLiteral(x, bw)) =>
                                wrapBv(-x, bw)
                        }
                    }
                }
            }
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
