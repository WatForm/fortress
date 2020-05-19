package fortress.solverinterface

import com.microsoft.z3.{
    Context => Z3Context,
    Solver => Z3Solver,
    Sort => Z3Sort,
    FuncDecl => Z3FuncDecl,
    Expr => Z3Expr,
    BoolExpr => Z3BoolExpr,
    ArithExpr => Z3ArithExpr,
    BitVecExpr => Z3BitVecExpr,
    IntExpr => Z3IntExpr
}

import fortress.msfol._
import fortress.operations.TermVisitorWithTypeContext

import scala.jdk.CollectionConverters._

import fortress.util.Errors

// Precondition: theory must be typechecked and all declarations must
// be internally consistent
class TheoryToZ3(theory: Theory) {
    
    val config = Map(
        "model" -> "true" // How does this affect performance?
    )
    val context = new Z3Context(config.asJava)
    
    def sortConversions(s: Sort): Z3Sort = s match {
        case SortConst(name) => context.mkUninterpretedSort(name)
        case BoolSort => context.getBoolSort
        case IntSort => context.getIntSort
        case BitVectorSort(bitwidth) => context.mkBitVecSort(bitwidth)
    }
    
    val constantConversionsMap: Map[String, Z3FuncDecl] = {
        val tuples = for(constant <- theory.constants) yield {
            val z3Sort = sortConversions(constant.sort)
            val z3Decl = context.mkConstDecl(constant.name, z3Sort)
            (constant.name, z3Decl)
        }
        tuples.toMap
    }
    
    def fdecltoZ3Decl(fdecl: FuncDecl): Z3FuncDecl = {
        val z3ArgSorts: Array[Z3Sort] = fdecl.argSorts.map(sortConversions).toArray
        val z3ResultSort = sortConversions(fdecl.resultSort)
        val z3Decl = context.mkFuncDecl(fdecl.name, z3ArgSorts, z3ResultSort)
        z3Decl
    }
    
    val functionConversionsMap: Map[String, Z3FuncDecl] = {
        val tuples = for(fdecl <- theory.functionDeclarations) yield (fdecl.name, fdecltoZ3Decl(fdecl))
        tuples.toMap
    }
    
    def convert: (Z3Context, Z3Solver) = {
        val solver  = context.mkSolver("QF_UFNIA") // How does changing the logic affect the efficiency?

        for(axiom <- theory.axioms) {
            val formula: Z3BoolExpr = convertAxiom(axiom).asInstanceOf[Z3BoolExpr]
            solver.add(formula)
        }
        
        (context, solver)
    }

    def convertAxiom(axiom: Term): Z3BoolExpr = recur(axiom, List.empty).asInstanceOf[Z3BoolExpr]
    
    def lookupSort(variable: Var, ctxStack: List[AnnotatedVar]): Option[Sort] = {
        // Check if it is in the Context
        // Note that the context is used as a stack, so we just need to iterate
        // from front to back and not have to worry about shadowed variables.
        // e.g. in (forall v: A, forall v : B, p(v)), the context will look like
        // List[v: B, v: A], and the term will fail to typecheck if p : A -> Bool
        // since the use of v will have type B
        for(av <- ctxStack) {
            if(av.name == variable.name) {
                return Some(av.sort)
            }
        }
        
        // If it is not in the stack, check if is in the declared constants
        val constMaybe: Option[AnnotatedVar] = theory.signature.queryConstant(variable)
        if(constMaybe.nonEmpty) {
            Some(constMaybe.get.sort)
        } else {
            None
        }
    }
    
    def recur(term: Term, ctxStack: List[AnnotatedVar]): Z3Expr = term match {
        case Top => context.mkTrue()
        case Bottom => context.mkFalse()
        case IntegerLiteral(value) => context.mkInt(value)
        case BitVectorLiteral(value, bitwidth) => context.mkBV(value, bitwidth)
        case EnumValue(_) | DomainElement(_, _) => Errors.unreachable()
        case v @ Var(name) => {
            val z3Sort = sortConversions(lookupSort(v, ctxStack).get)
            context.mkConst(name, z3Sort)
        }
        case Not(body) => context.mkNot(recur(body, ctxStack).asInstanceOf[Z3BoolExpr])
        case AndList(args) => {
            val z3Args = args map (recur(_, ctxStack).asInstanceOf[Z3BoolExpr])
            context.mkAnd(z3Args:_*)
        }
        case OrList(args) => {
            val z3Args = args map (recur(_, ctxStack).asInstanceOf[Z3BoolExpr])
            context.mkOr(z3Args:_*)
        }
        case Distinct(args) => {
            val z3Args = args map (recur(_, ctxStack))
            context.mkDistinct(z3Args:_*)
        }
        case Implication(left, right) => context.mkImplies(
            recur(left, ctxStack).asInstanceOf[Z3BoolExpr],
            recur(right, ctxStack).asInstanceOf[Z3BoolExpr]
        )
        case Iff(left, right) => context.mkEq( // Z3 uses Eq for Iff
            recur(left, ctxStack).asInstanceOf[Z3BoolExpr],
            recur(right, ctxStack).asInstanceOf[Z3BoolExpr]
        )
        case Eq(left, right) => context.mkEq(
            recur(left, ctxStack),
            recur(right, ctxStack)
        )
        case App(fname, args) => {
            val z3Decl = functionConversionsMap(fname)
            val z3Args = args map (recur(_, ctxStack))
            z3Decl.apply(z3Args:_*)
        }
        case Exists(vars, body) => {
            val newCtxStack = vars.toList.reverse ::: ctxStack
            val z3Vars: Array[Z3Expr] = (vars map (av => recur(av.variable, newCtxStack))).toArray
            val z3Body = recur(body, newCtxStack)
            context.mkExists(
                z3Vars,
                z3Body,
                0, // Default weight of 0
                null, // No patterns
                null, // No anti-patterns
                null, // No symbol to track quantifier
                null // No symbol to track skolem constants
            )
        }
        case Forall(vars, body) => {
            val newCtxStack = vars.toList.reverse ::: ctxStack
            val z3Vars: Array[Z3Expr] = (vars map (av => recur(av.variable, newCtxStack))).toArray
            val z3Body = recur(body, newCtxStack)
            context.mkForall(
                z3Vars,
                z3Body,
                0, // Default weight of 0
                null, // No patterns
                null, // No anti-patterns
                null, // No symbol to track quantifier
                null // No symbol to track skolem constants
            )
        }
        case BuiltinApp(fn, args) => (fn, args) match {
            case (IntPlus, Seq(arg1, arg2)) => {
                context.mkAdd(
                    recur(arg1, ctxStack).asInstanceOf[Z3IntExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (IntNeg, Seq(arg)) => {
                context.mkUnaryMinus(recur(arg, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (IntSub, Seq(arg1, arg2)) => {
                context.mkSub(
                    recur(arg1, ctxStack).asInstanceOf[Z3IntExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (IntMult, Seq(arg1, arg2)) => {
                context.mkMul(
                    recur(arg1, ctxStack).asInstanceOf[Z3IntExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (IntDiv, Seq(arg1, arg2)) => {
                context.mkDiv(
                    recur(arg1, ctxStack).asInstanceOf[Z3IntExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (IntMod, Seq(arg1, arg2)) => {
                context.mkMod(
                    recur(arg1, ctxStack).asInstanceOf[Z3IntExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (IntLE, Seq(arg1, arg2)) => {
                context.mkLe(
                    recur(arg1, ctxStack).asInstanceOf[Z3IntExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (IntLT, Seq(arg1, arg2)) => {
                context.mkLt(
                    recur(arg1, ctxStack).asInstanceOf[Z3IntExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (IntGE, Seq(arg1, arg2)) => {
                context.mkGe(
                    recur(arg1, ctxStack).asInstanceOf[Z3IntExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (IntGT, Seq(arg1, arg2)) => {
                context.mkGt(
                    recur(arg1, ctxStack).asInstanceOf[Z3IntExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3IntExpr])
            }
            case (BvPlus, Seq(arg1, arg2)) => {
                context.mkBVAdd(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvNeg, Seq(arg)) => {
                context.mkBVNeg(recur(arg, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvSub, Seq(arg1, arg2)) => {
                context.mkBVSub(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvMult, Seq(arg1, arg2)) => {
                context.mkBVMul(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvSignedDiv, Seq(arg1, arg2)) => {
                context.mkBVSDiv(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvSignedRem, Seq(arg1, arg2)) => {
                context.mkBVSRem(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvSignedMod, Seq(arg1, arg2)) => {
                context.mkBVSMod(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvSignedLE, Seq(arg1, arg2)) => {
                context.mkBVSLE(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvSignedLT, Seq(arg1, arg2)) => {
                context.mkBVSLT(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvSignedGE, Seq(arg1, arg2)) => {
                context.mkBVSGE(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case (BvSignedGT, Seq(arg1, arg2)) => {
                context.mkBVSGT(
                    recur(arg1, ctxStack).asInstanceOf[Z3BitVecExpr],
                    recur(arg2, ctxStack).asInstanceOf[Z3BitVecExpr])
            }
            case _ => Errors.unreachable()
        }
    }
}
