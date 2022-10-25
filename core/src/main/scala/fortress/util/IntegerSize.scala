package fortress.util

import fortress.msfol._
import fortress.util.Errors

import fortress.util.Extensions.IntExtension

object IntegerSize {
    /** Finds the bitvector width of a given term. */
    def bitvectorWidth(term: Term, sig: Signature): Option[Int] = term match {
        case BitVectorLiteral(_, bitwidth) => Some(bitwidth)
        case Var(x) => sig.queryConstant(Var(x)) match {
            case Some(AnnotatedVar(_, sort)) => bitvectorWidthOfSort(sort)
            case None => None
        }
        case App(functionName, _) => sig.queryUninterpretedFunction(functionName) match {
            case Some(FuncDecl(_,_, resultSort)) => bitvectorWidthOfSort(resultSort)
            case _ => None
        }
        case DomainElement(_, sort) => bitvectorWidthOfSort(sort)
        case BuiltinApp(function, arguments) => function match {
            case BvConcat => Some(arguments.map(bitvectorWidth(_, sig)).map(_.get).fold(0)(_ + _))
            case BvMult => bitvectorWidth(arguments(0), sig)
            case BvNeg => bitvectorWidth(arguments(0), sig)
            case BvPlus => bitvectorWidth(arguments(0), sig)
            case BvSignedDiv => bitvectorWidth(arguments(0), sig)
            case BvSignedMod => bitvectorWidth(arguments(0), sig)
            case BvSignedRem => bitvectorWidth(arguments(0), sig)
            case BvSub => bitvectorWidth(arguments(0), sig)
            case _ => None
        }
        case _ => Errors.Internal.impossibleState("Trying to get bitwidth of '" + term.toString() + "'")
    }
    /** The minimum value which can be stored in a two's complement bitvector of width `bitwidth`. */
    def minimumIntValue(bitwidth: Int): Int = -(2 ** (bitwidth - 1))
    /** The maximum value which can be stored in a two's complement bitvector of width `bitwidth`. */
    def maximumIntValue(bitwidth: Int): Int = (2 ** (bitwidth - 1)) - 1

    def bitvectorWidthOfSort(sort: Sort): Option[Int] = sort match {
        case BitVectorSort(width) => Some(width)
        case _ => Errors.Internal.impossibleState("Cannot get bitwidth of non-bitvector! Got " + sort.toString() + " instead.")
    }
}