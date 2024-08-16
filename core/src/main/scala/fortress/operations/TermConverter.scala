package fortress.operations

import fortress.msfol._
import fortress.util.Errors

object TermConverter {
    /** Converts integers and operations on integers into signed bitvectors and
      * signed bitvector operations. */
    def intToSignedBitVector(term: Term, bitwidth: Int): Term = {
       object IntToSignedBitVector extends NaturalTermRecursion {
           override val exceptionalMappings: PartialFunction[Term, Term] = {
               case IntegerLiteral(value) => BitVectorLiteral(value, bitwidth)
               case BuiltinApp(IntPlus, args) => BuiltinApp(BvPlus, args map naturalRecur)
               case BuiltinApp(IntNeg, args) => BuiltinApp(BvNeg, args map naturalRecur)
               case BuiltinApp(IntSub, args) => BuiltinApp(BvSub, args map naturalRecur)
               case BuiltinApp(IntMult, args) => BuiltinApp(BvMult, args map naturalRecur)
               case BuiltinApp(IntDiv, args) => BuiltinApp(BvSignedDiv, args map naturalRecur)
               case BuiltinApp(IntMod, args) => BuiltinApp(BvSignedMod, args map naturalRecur)
               case BuiltinApp(IntLE, args) => BuiltinApp(BvSignedLE, args map naturalRecur)
               case BuiltinApp(IntLT, args) => BuiltinApp(BvSignedLT, args map naturalRecur)
               case BuiltinApp(IntGE, args) => BuiltinApp(BvSignedGE, args map naturalRecur)
               case BuiltinApp(IntGT, args) => BuiltinApp(BvSignedGT, args map naturalRecur)
               case BuiltinApp(IntEQ, args) => BuiltinApp(BvEQ, args map naturalRecur)
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
       IntToSignedBitVector.apply(term)
    }
}
