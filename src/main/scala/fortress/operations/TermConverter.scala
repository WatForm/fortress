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
    
    def simplify(term: Term): Term = {
        def simplifyStep(term: Term): Term = term match {
            case Not(Bottom) => Top
            case Not(Top) => Bottom
            case Not(Not(body)) => body
            case AndList(args) => {
                if (args.exists(t => t == Bottom))
                    Bottom
                else {
                    val newArgs = args.filter(t => t != Top)
                    if (newArgs.size == 0) Top else AndList(newArgs)
                }
            }
            case OrList(args) => {
                if (args.exists(t => t == Top))
                    Top
                else {
                    val newArgs = args.filter(t => t != Bottom)
                    if (newArgs.size == 0) Bottom else OrList(newArgs)
                }
            }
            case Implication(Bottom, _) => Top
            case Implication(_, Top) => Top
            case Implication(Top, p) => p
            case Implication(p, Bottom) => Not(p)
            case Iff(p, Top) => p
            case Iff(Top, p) => p
            case Iff(p, Bottom) => Not(p)
            case Iff(Bottom, p) => Not(p)
            case Eq(d1 @ DomainElement(_, _), d2 @ DomainElement(_, _)) => if (d1 == d2) Top else Bottom
            case Eq(left, right) => if (left == right) Top else term
            // Note that we don't need a signature to check below whether the free
            // free variable is really or a constant. We just want to check if
            // the quantified variable x is within the set of free vars.
            // If x is within free vars union constants, then since it is quantified
            // here it must be a free var.
            case Exists(vars, body) => {
                val freeVars: java.util.Set[Var] = body.freeVarConstSymbolsJava
                val newVars = vars.filter((av: AnnotatedVar) => freeVars.contains(av.variable))
                if (newVars.size == 0)
                    body
                else
                    Exists(newVars, body)
            }
            case Forall(vars, body) => {
                val freeVars: java.util.Set[Var] = body.freeVarConstSymbolsJava
                val newVars = vars.filter((av: AnnotatedVar) => freeVars.contains(av.variable))
                if (newVars.size == 0)
                    body
                else
                    Forall(newVars, body)
            }
            case _ => term
        }
        
        def simplifyFull(term: Term): Term = term match {
            case Not(body) => simplifyStep(Not(simplifyFull(body)))
            case AndList(args) => simplifyStep(AndList(args.map(simplifyFull)))
            case OrList(args) => simplifyStep(OrList(args.map(simplifyFull)))
            case Implication(left, right) => simplifyStep(Implication(simplifyFull(left), simplifyFull(right)))
            case Iff(left, right) => simplifyStep(Iff(simplifyFull(left), simplifyFull(right)))
            case Distinct(args) => simplifyStep(Distinct(args.map(simplifyFull)))
            case Exists(vars, body) => simplifyStep(Exists(vars, simplifyFull(body)))
            case Forall(vars, body) => simplifyStep(Forall(vars, simplifyFull(body)))
            // We consider applications and equals to be atomic and have non-Boolean arguments
            // so we need not recurse on their arguments
            case Eq(_, _) | App(_, _) | BuiltinApp(_, _) => simplifyStep(term)
            case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _)
                | IntegerLiteral(_) | BitVectorLiteral(_, _) => term
        }
        
        simplifyFull(term)
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
