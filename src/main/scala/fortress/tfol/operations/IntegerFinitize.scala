package fortress.tfol.operations

import fortress.tfol._
import fortress.tfol.IntegerExtension._
import fortress.tfol.BitVectorExtension._
import scala.collection.immutable.Seq // Use immutable seq
 
class IntToSignedBitVector(bitwidth: Int) extends NaturalTermRecursion {
    override val exceptionalMappings: PartialFunction[Term, Term] = {
        case IntegerLiteral(value) => BitVectorLiteral(value, bitwidth)
        case App(`plus`, args) => App(bvadd, args)
        case App(`minus`, args) if args.size == 1 => App(bvneg, args map naturalRecur)
        case App(`minus`, args) => App(bvsub, args map naturalRecur)
        case App(`times`, args) => App(bvmul, args map naturalRecur)
        case App(`div`, args) => App(bvsdiv, args map naturalRecur)
        case App(`mod`, args) => App(bvsmod, args map naturalRecur)
        case App(`LE`, args) => App(bvsle, args map naturalRecur)
        case App(`LT`, args) => App(bvslt, args map naturalRecur)
        case App(`GE`, args) => App(bvsge, args map naturalRecur)
        case App(`GT`, args) => App(bvsgt, args map naturalRecur)
        case Exists(vars, body) => {
            val newVars = vars.map(
                v => if (v.sort == IntSort) { v.variable of BitVectorSort(bitwidth) } else v
            )
            Exists(newVars, naturalRecur(body))
        }
        case Forall(vars, body) => {
            val newVars = vars.map(
                v => if (v.sort == IntSort) { v.variable of BitVectorSort(bitwidth) } else v
            )
            Forall(newVars, naturalRecur(body))
        }
    }
    
    def apply(term: Term): Term = naturalRecur(term)
}
