package fortress.operations

import fortress.msfol._
import fortress.util.Errors

object TermConverter {
    /** Returns the negation normal form of a term. 
      * It is assumed that Eq is not used on sort Bool and so uses of Eq are atomic.
      * Additionally it is assumed that applications and arguments to applications
      * are atomic. */
    def nnf(term: Term): Term = term match {
        case AndList(args) => AndList(args.map(nnf))
        case OrList(args) => OrList(args.map(nnf))
        case (distinct: Distinct) => nnf(distinct.asPairwiseNotEquals)
        case Implication(p, q) => OrList(nnf(Not(p)), nnf(q))
        case Iff(p, q) => OrList(
            AndList(nnf(p), nnf(q)),
            AndList(nnf(Not(p)), nnf(Not(q)))
        )
        case Forall(vars, body) => Forall(vars, nnf(body))
        case Exists(vars, body) => Exists(vars, nnf(body))
        case Not(Top) => Bottom
        case Not(Bottom) => Top
        case Not(Not(p)) => nnf(p)
        case Not(AndList(args)) => OrList(args.map(arg => nnf(Not(arg))))
        case Not(OrList(args)) => AndList(args.map(arg => nnf(Not(arg))))
        case Not(distinct @ Distinct(_)) => nnf(Not(distinct.asPairwiseNotEquals))
        case Not(Implication(p, q)) => AndList(nnf(p), nnf(Not(q)))
        case Not(Iff(p, q)) => OrList(
            AndList(nnf(p), nnf(Not(q))),
            AndList(nnf((Not(p))), nnf(q))
        )
        case Not(Forall(vars, body)) => Exists(vars, nnf(Not(body)))
        case Not(Exists(vars, body)) => Forall(vars, nnf(Not(body)))
        case Top | Bottom | Var(_) | App(_, _) | BuiltinApp(_, _) | Eq(_, _) | DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
            | Not(Var(_)) | Not(App(_, _)) | Not(BuiltinApp(_, _)) | Not(Eq(_, _)) => term
        case Not(DomainElement(_, _)) | Not(IntegerLiteral(_))
            |  Not(BitVectorLiteral(_, _)) | Not(EnumValue(_)) => ???
    }
    
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
